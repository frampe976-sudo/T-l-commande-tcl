// Telecommande WiFi pour TV TCL / Android TV / Google TV
// Protocole : Android TV Remote v2 (TLS + protobuf, ports 6467 appairage / 6466 commandes)
//
// Tout est dans un seul fichier pour faciliter le copier-coller depuis un telephone.

import 'dart:async';
import 'dart:convert';
import 'dart:io';
import 'dart:typed_data';

// Imports volontairement restreints : basic_utils reexporte PointyCastle, dont
// les classes Key et Digest entrent en collision avec Flutter et crypto.
import 'package:basic_utils/basic_utils.dart' show CryptoUtils, X509Utils;
import 'package:crypto/crypto.dart' show sha256;
// ValueListenable et compute() vivent ici, pas dans material.dart.
import 'package:flutter/foundation.dart';
import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:pointycastle/export.dart' show RSAPrivateKey, RSAPublicKey;
import 'package:shared_preferences/shared_preferences.dart';

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  runApp(const RemoteApp());
}

// ===========================================================================
// 1. COUCHE PROTOCOLE : encodage varint et decoupage des messages
// ===========================================================================

/// Encode un entier au format varint protobuf (base 128, 7 bits utiles par octet).
List<int> encodeVarint(int value) {
  final out = <int>[];
  var v = value;
  while (true) {
    if (v < 0x80) {
      out.add(v);
      return out;
    }
    out.add((v & 0x7F) | 0x80);
    v >>= 7;
  }
}

/// Resultat de la lecture d'un varint : sa valeur et le nombre d'octets consommes.
class _Varint {
  final int value;
  final int size;
  const _Varint(this.value, this.size);
}

_Varint? _readVarint(List<int> buf, int offset) {
  var value = 0;
  var shift = 0;
  var i = offset;
  while (true) {
    if (i >= buf.length) return null; // incomplet
    final b = buf[i];
    value |= (b & 0x7F) << shift;
    i++;
    if ((b & 0x80) == 0) return _Varint(value, i - offset);
    shift += 7;
    if (shift > 35) return null;
  }
}

/// Chaque message du protocole est precede de sa taille en varint.
/// Cette classe accumule les octets recus et ressort les messages complets.
class FrameReader {
  final List<int> _buf = [];

  void add(List<int> data) => _buf.addAll(data);

  /// Retourne le prochain message complet, ou null s'il en manque des octets.
  List<int>? next() {
    if (_buf.isEmpty) return null;
    final len = _readVarint(_buf, 0);
    if (len == null) return null;
    final total = len.size + len.value;
    if (_buf.length < total) return null;
    final msg = _buf.sublist(len.size, total);
    _buf.removeRange(0, total);
    return msg;
  }
}

/// Construit une trame prete a envoyer : taille en varint puis charge utile.
List<int> frame(List<int> payload) => [...encodeVarint(payload.length), ...payload];

// ===========================================================================
// 2. CERTIFICATS : generation du certificat client, lecture de celui de la TV
// ===========================================================================

class ClientIdentity {
  final String certPem;
  final String keyPem;
  final Uint8List modulus;
  final Uint8List exponent;

  const ClientIdentity({
    required this.certPem,
    required this.keyPem,
    required this.modulus,
    required this.exponent,
  });
}

/// Retire les zeros de tete, comme le fait l'implementation Android de reference.
Uint8List stripLeadingZeros(Uint8List input) {
  var i = 0;
  while (i < input.length - 1 && input[i] == 0) {
    i++;
  }
  return Uint8List.sublistView(input, i);
}

Uint8List bigIntToBytes(BigInt value) {
  var hex = value.toRadixString(16);
  if (hex.length.isOdd) hex = '0$hex';
  final out = Uint8List(hex.length ~/ 2);
  for (var i = 0; i < out.length; i++) {
    out[i] = int.parse(hex.substring(i * 2, i * 2 + 2), radix: 16);
  }
  return stripLeadingZeros(out);
}

/// Genere une paire RSA 2048 et un certificat auto-signe.
/// Lent (plusieurs secondes) : a lancer dans un isolate via compute().
ClientIdentity generateClientIdentity(String commonName) {
  final pair = CryptoUtils.generateRSAKeyPair(keySize: 2048);
  final privateKey = pair.privateKey as RSAPrivateKey;
  final publicKey = pair.publicKey as RSAPublicKey;

  // Les memes attributs que la vraie application Google TV Remote.
  final dn = {
    'CN': commonName,
    'O': 'Google Inc.',
    'OU': 'Android',
    'L': 'Mountain View',
    'ST': 'California',
    'C': 'US',
  };

  final csr = X509Utils.generateRsaCsrPem(dn, privateKey, publicKey);
  final certPem = X509Utils.generateSelfSignedCertificate(privateKey, csr, 3650);
  final keyPem = CryptoUtils.encodeRSAPrivateKeyToPem(privateKey);

  return ClientIdentity(
    certPem: certPem,
    keyPem: keyPem,
    modulus: bigIntToBytes(publicKey.modulus!),
    exponent: bigIntToBytes(publicKey.exponent!),
  );
}

/// Cle publique RSA extraite d'un certificat X.509.
class RsaPublicParams {
  final Uint8List modulus;
  final Uint8List exponent;
  const RsaPublicParams(this.modulus, this.exponent);
}

class _Tlv {
  final int tag;
  final int start;
  final int length;
  int get end => start + length;
  const _Tlv(this.tag, this.start, this.length);
}

_Tlv _readTlv(Uint8List d, int offset) {
  final tag = d[offset];
  var i = offset + 1;
  var len = d[i];
  i++;
  if ((len & 0x80) != 0) {
    final n = len & 0x7F;
    len = 0;
    for (var k = 0; k < n; k++) {
      len = (len << 8) | d[i];
      i++;
    }
  }
  return _Tlv(tag, i, len);
}

/// Extrait le modulus et l'exposant RSA d'un certificat X.509 au format DER.
///
/// On parcourt les champs du TBSCertificate et on reconnait le
/// SubjectPublicKeyInfo a sa structure : une SEQUENCE dont le premier enfant
/// est une SEQUENCE (l'algorithme) et le second une BIT STRING (la cle).
RsaPublicParams rsaParamsFromCertificate(Uint8List der) {
  final certificate = _readTlv(der, 0);
  final tbs = _readTlv(der, certificate.start);

  var i = tbs.start;
  while (i < tbs.end) {
    final field = _readTlv(der, i);
    if (field.tag == 0x30) {
      try {
        final algorithm = _readTlv(der, field.start);
        if (algorithm.tag == 0x30 && algorithm.end < field.end) {
          final bitString = _readTlv(der, algorithm.end);
          if (bitString.tag == 0x03) {
            // Le premier octet d'une BIT STRING compte les bits inutilises.
            final seq = _readTlv(der, bitString.start + 1);
            if (seq.tag == 0x30) {
              final modulus = _readTlv(der, seq.start);
              final exponent = _readTlv(der, modulus.end);
              return RsaPublicParams(
                stripLeadingZeros(
                    Uint8List.sublistView(der, modulus.start, modulus.end)),
                stripLeadingZeros(
                    Uint8List.sublistView(der, exponent.start, exponent.end)),
              );
            }
          }
        }
      } catch (_) {
        // Ce champ n'etait pas le bon, on continue.
      }
    }
    i = field.end;
  }
  throw const FormatException(
      "Cle publique RSA introuvable dans le certificat de la TV");
}

SecurityContext buildSecurityContext(String certPem, String keyPem) {
  return SecurityContext(withTrustedRoots: false)
    ..useCertificateChainBytes(utf8.encode(certPem))
    ..usePrivateKeyBytes(utf8.encode(keyPem));
}

// ===========================================================================
// 3. CONNEXION : lecture message par message
// ===========================================================================

class ProtocolConnection {
  final SecureSocket socket;
  final FrameReader _reader = FrameReader();
  final List<List<int>> _pending = [];
  final List<Completer<List<int>>> _waiting = [];
  Object? _error;
  bool _closed = false;

  ProtocolConnection(this.socket) {
    socket.listen(
      (data) {
        _reader.add(data);
        while (true) {
          final msg = _reader.next();
          if (msg == null) break;
          if (_waiting.isNotEmpty) {
            _waiting.removeAt(0).complete(msg);
          } else {
            _pending.add(msg);
          }
        }
      },
      onError: _fail,
      onDone: () => _fail(const SocketException('Connexion fermee par la TV')),
      cancelOnError: true,
    );
  }

  void _fail(Object error) {
    _error = error;
    _closed = true;
    for (final w in _waiting) {
      if (!w.isCompleted) w.completeError(error);
    }
    _waiting.clear();
  }

  /// Flux continu des messages. Pas de delai d'attente : une session de
  /// telecommande peut rester inactive plusieurs minutes.
  Stream<List<int>> get messages async* {
    while (!_closed || _pending.isNotEmpty) {
      yield await next(timeout: null);
    }
  }

  Future<List<int>> next({Duration? timeout = const Duration(seconds: 20)}) {
    if (_pending.isNotEmpty) return Future.value(_pending.removeAt(0));
    if (_error != null) return Future.error(_error!);
    final completer = Completer<List<int>>();
    _waiting.add(completer);
    if (timeout == null) return completer.future;
    return completer.future.timeout(timeout, onTimeout: () {
      _waiting.remove(completer);
      throw TimeoutException("La TV n'a pas repondu");
    });
  }

  void send(List<int> payload) => socket.add(frame(payload));

  Future<void> close() async {
    _closed = true;
    try {
      await socket.close();
    } catch (_) {}
    socket.destroy();
  }
}

// ===========================================================================
// 4. APPAIRAGE (port 6467)
// ===========================================================================

class PairingException implements Exception {
  final String message;
  const PairingException(this.message);
  @override
  String toString() => message;
}

/// Verifie l'entete commun : version de protocole 2 et statut OK (200).
void _checkStatus(List<int> msg) {
  // Attendu en tete : 8, 2 (version) puis 16, 200, 1 (statut OK)
  if (msg.length < 5 || msg[0] != 8 || msg[2] != 16) {
    throw const PairingException("Reponse inattendue de la TV");
  }
  final status = _readVarint(msg, 3);
  if (status == null || status.value != 200) {
    final code = status?.value;
    if (code == 402) {
      throw const PairingException(
          "Code refuse par la TV. Verifie les 6 caracteres et reessaie.");
    }
    throw PairingException("La TV a refuse l'appairage (statut $code)");
  }
}

class PairingClient {
  final String host;
  final int port;
  final String serviceName;
  final String deviceName;

  ProtocolConnection? _conn;
  ClientIdentity? _identity;
  RsaPublicParams? _serverKey;

  PairingClient({
    required this.host,
    this.port = 6467,
    this.serviceName = 'com.andhime.atvremote',
    this.deviceName = 'Telecommande',
  });

  /// Etapes 1 a 3 : la TV finit par afficher un code de 6 caracteres.
  Future<void> start(ClientIdentity identity) async {
    _identity = identity;

    final socket = await SecureSocket.connect(
      host,
      port,
      context: buildSecurityContext(identity.certPem, identity.keyPem),
      onBadCertificate: (_) => true, // la TV a un certificat auto-signe
      timeout: const Duration(seconds: 10),
    );

    try {
      final peer = socket.peerCertificate;
      if (peer == null) {
        throw const PairingException(
            "Impossible de lire le certificat de la TV");
      }
      _serverKey = rsaParamsFromCertificate(Uint8List.fromList(peer.der));
    } catch (_) {
      socket.destroy();
      rethrow;
    }
    _conn = ProtocolConnection(socket);

    // --- 1) PairingRequest -------------------------------------------------
    final service = utf8.encode(serviceName);
    final client = utf8.encode(deviceName);
    final request = <int>[
      8, 2, // version du protocole = 2
      16, 200, 1, // statut OK
      82, 2 + service.length + 2 + client.length, // champ 10 : PairingRequest
      10, service.length, ...service, // service_name
      18, client.length, ...client, // client_name
    ];
    _conn!.send(request);
    _checkStatus(await _conn!.next());

    // --- 2) PairingOption --------------------------------------------------
    // encodage hexadecimal (3), 6 symboles, role INPUT (1)
    _conn!.send([8, 2, 16, 200, 1, 162, 1, 8, 10, 4, 8, 3, 16, 6, 24, 1]);
    _checkStatus(await _conn!.next());

    // --- 3) PairingConfiguration ------------------------------------------
    _conn!.send([8, 2, 16, 200, 1, 242, 1, 8, 10, 4, 8, 3, 16, 6, 16, 1]);
    _checkStatus(await _conn!.next());
    // La TV affiche maintenant le code a l'ecran.
  }

  /// Etape 4 : envoi du secret calcule a partir du code affiche sur la TV.
  Future<void> sendCode(String code) async {
    final conn = _conn;
    final identity = _identity;
    final serverKey = _serverKey;
    if (conn == null || identity == null || serverKey == null) {
      throw const PairingException("Appairage non demarre");
    }

    final clean = code.trim().replaceAll(' ', '').toUpperCase();
    if (clean.length != 6 || !RegExp(r'^[0-9A-F]{6}$').hasMatch(clean)) {
      throw const PairingException(
          "Le code doit faire 6 caracteres hexadecimaux (0-9, A-F)");
    }

    // Les 2 premiers caracteres sont une somme de controle : on garde les 4 derniers.
    final nonce = <int>[];
    for (var i = 2; i < 6; i += 2) {
      nonce.add(int.parse(clean.substring(i, i + 2), radix: 16));
    }

    // SHA-256 sur la concatenation : modulus et exposant du client, puis ceux
    // de la TV, puis les 2 octets issus du code affiche a l'ecran.
    final secret = sha256.convert(<int>[
      ...identity.modulus,
      ...identity.exponent,
      ...serverKey.modulus,
      ...serverKey.exponent,
      ...nonce,
    ]).bytes;

    conn.send([
      8, 2,
      16, 200, 1,
      194, 2, 34, // champ 40 : PairingSecret
      10, 32, // champ 1 : bytes de 32 octets
      ...secret,
    ]);
    _checkStatus(await conn.next());
  }

  Future<void> dispose() async => _conn?.close();
}

// ===========================================================================
// 5. SESSION TELECOMMANDE (port 6466)
// ===========================================================================

/// Direction d'une touche : 1 = appui, 2 = relachement, 3 = appui court.
class KeyDirection {
  static const int start = 1;
  static const int end = 2;
  static const int short = 3;
}

class RemoteClient {
  final String host;
  final int port;
  final String packageName;
  final String appVersion;

  ProtocolConnection? _conn;
  StreamSubscription? _sub;

  final _powered = ValueNotifier<bool?>(null);
  final _volume = ValueNotifier<VolumeInfo?>(null);
  final _currentApp = ValueNotifier<String?>(null);
  final _connected = ValueNotifier<bool>(false);

  ValueListenable<bool?> get powered => _powered;
  ValueListenable<VolumeInfo?> get volume => _volume;
  ValueListenable<String?> get currentApp => _currentApp;
  ValueListenable<bool> get connected => _connected;

  void Function(Object error)? onDisconnected;

  RemoteClient({
    required this.host,
    this.port = 6466,
    this.packageName = 'com.andhime.atvremote',
    this.appVersion = '1.0.0',
  });

  Future<void> connect(ClientIdentity identity) async {
    final socket = await SecureSocket.connect(
      host,
      port,
      context: buildSecurityContext(identity.certPem, identity.keyPem),
      onBadCertificate: (_) => true,
      timeout: const Duration(seconds: 10),
    );
    final conn = ProtocolConnection(socket);
    _conn = conn;

    // La TV envoie d'abord son propre message de configuration.
    await conn.next(timeout: const Duration(seconds: 10));

    // --- 1re configuration : on decline notre identite --------------------
    final model = utf8.encode('Telecommande');
    final vendor = utf8.encode('Android');
    final version = utf8.encode('1');
    final package = utf8.encode(packageName);
    final appVer = utf8.encode(appVersion);
    final deviceInfo = <int>[
      10, model.length, ...model, // champ 1 : modele
      18, vendor.length, ...vendor, // champ 2 : fabricant
      24, 1, // champ 3
      34, version.length, ...version, // champ 4 : version
      42, package.length, ...package, // champ 5 : nom du paquet
      50, appVer.length, ...appVer, // champ 6 : version applicative
    ];
    final configure = <int>[
      8, 238, 4, // champ 1 : code 622
      18, deviceInfo.length, ...deviceInfo, // champ 2 : device_info
    ];
    conn.send([10, configure.length, ...configure]);

    // La TV repond par son accuse puis un message vide [18, 0].
    await conn.next(timeout: const Duration(seconds: 10));

    // --- 2e configuration : on active la session --------------------------
    conn.send([18, 3, 8, 238, 4]);

    _connected.value = true;
    _sub = conn.messages.listen(_handleMessage, onError: (Object e) {
      _connected.value = false;
      onDisconnected?.call(e);
    });
  }

  void _handleMessage(List<int> msg) {
    if (msg.isEmpty) return;
    switch (msg[0]) {
      case 66: // remote_ping_request : il faut repondre sinon la TV coupe
        _replyToPing(msg);
        break;
      case 194: // etat d'alimentation
        if (msg.length >= 5 && msg[1] == 2) {
          _powered.value = msg[4] == 1;
        }
        break;
      case 162: // application en cours
        _currentApp.value = _readNestedString(msg);
        break;
      case 146: // volume
        _volume.value = VolumeInfo.parse(msg);
        break;
    }
  }

  void _replyToPing(List<int> msg) {
    // Format : [66, taille, 8, <val1>, 16, <val2>] ; on renvoie val1.
    var val = 25;
    if (msg.length > 3 && msg[2] == 8) {
      val = _readVarint(msg, 3)?.value ?? 25;
    }
    final body = [8, ...encodeVarint(val)];
    _conn?.send([74, body.length, ...body]);
  }

  String? _readNestedString(List<int> msg) {
    try {
      // [162, 1, taille, 10, taille, <octet inconnu>, 18, taille, texte...]
      final idx = msg.indexOf(18, 3);
      if (idx < 0 || idx + 1 >= msg.length) return null;
      final len = msg[idx + 1];
      if (idx + 2 + len > msg.length) return null;
      return utf8.decode(msg.sublist(idx + 2, idx + 2 + len),
          allowMalformed: true);
    } catch (_) {
      return null;
    }
  }

  void _sendKey(int keyCode, int direction) {
    final body = [8, ...encodeVarint(keyCode), 16, direction];
    _conn?.send([82, body.length, ...body]);
  }

  /// Appui court sur une touche : appui puis relachement.
  void pressKey(int keyCode) {
    _sendKey(keyCode, KeyDirection.start);
    _sendKey(keyCode, KeyDirection.end);
  }

  /// Certaines touches (chaine +/-) attendent un seul message en mode court.
  void tapKey(int keyCode) => _sendKey(keyCode, KeyDirection.short);

  /// Appui maintenu : certaines TV n'ouvrent leurs menus qu'a l'appui long.
  Future<void> longPressKey(int keyCode,
      {Duration hold = const Duration(milliseconds: 900)}) async {
    _sendKey(keyCode, KeyDirection.start);
    await Future.delayed(hold);
    _sendKey(keyCode, KeyDirection.end);
  }

  /// Lance une application via son lien profond.
  void launchApp(String deepLink) {
    final link = utf8.encode(deepLink);
    final body = [10, link.length, ...link];
    _conn?.send([210, 5, body.length, ...body]);
  }

  /// Saisit du texte lettre par lettre via les codes touches Android.
  void typeText(String text) {
    for (final char in text.toLowerCase().split('')) {
      final code = KeyCodes.forCharacter(char);
      if (code != null) pressKey(code);
    }
  }

  Future<void> dispose() async {
    _connected.value = false;
    await _sub?.cancel();
    await _conn?.close();
  }
}

class VolumeInfo {
  final int level;
  final int max;
  final bool muted;
  const VolumeInfo(this.level, this.max, this.muted);

  static VolumeInfo? parse(List<int> msg) {
    try {
      // [146, 3, taille, 8, <niveau>, 16, <max>, 26, <taille>, <nom>, 32, <mute>]
      var i = 3;
      var level = 0, max = 0;
      var muted = false;
      while (i < msg.length) {
        final tag = msg[i];
        if (tag == 8) {
          final v = _readVarint(msg, i + 1)!;
          level = v.value;
          i += 1 + v.size;
        } else if (tag == 16) {
          final v = _readVarint(msg, i + 1)!;
          max = v.value;
          i += 1 + v.size;
        } else if (tag == 26) {
          i += 2 + msg[i + 1];
        } else if (tag == 32) {
          final v = _readVarint(msg, i + 1)!;
          muted = v.value == 1;
          i += 1 + v.size;
        } else {
          break;
        }
      }
      if (max == 0) return null;
      return VolumeInfo(level, max, muted);
    } catch (_) {
      return null;
    }
  }
}

// ===========================================================================
// 6. CODES TOUCHES ANDROID
// ===========================================================================

class KeyCodes {
  static const int power = 26;
  static const int home = 3;
  static const int back = 4;
  static const int menu = 82;
  static const int dpadUp = 19;
  static const int dpadDown = 20;
  static const int dpadLeft = 21;
  static const int dpadRight = 22;
  static const int dpadCenter = 23;
  static const int volumeUp = 24;
  static const int volumeDown = 25;
  static const int volumeMute = 164;
  static const int channelUp = 166;
  static const int channelDown = 167;
  static const int playPause = 85;
  static const int stop = 86;
  static const int next = 87;
  static const int previous = 88;
  static const int rewind = 89;
  static const int fastForward = 90;
  static const int tvInput = 178;
  static const int settings = 176;
  static const int guide = 172;
  static const int info = 165;
  static const int search = 84;
  static const int assist = 219;
  static const int del = 67;
  static const int space = 62;
  static const int enter = 66;

  /// Code touche Android pour un caractere saisi au clavier.
  static int? forCharacter(String char) {
    if (char == ' ') return space;
    final code = char.codeUnitAt(0);
    if (code >= 97 && code <= 122) return 29 + (code - 97); // a..z -> 29..54
    if (code >= 48 && code <= 57) return 7 + (code - 48); // 0..9 -> 7..16
    return null;
  }
}

/// Une touche candidate a essayer. Les TV n'implementent pas toutes les memes :
/// le selecteur de source et les reglages varient beaucoup d'un modele a l'autre.
class KeyCandidate {
  final String label;
  final int code;
  final String technicalName;
  const KeyCandidate(this.label, this.code, this.technicalName);
}

const inputCandidates = <KeyCandidate>[
  KeyCandidate('Selecteur de source', 178, 'TV_INPUT'),
  KeyCandidate('HDMI 1', 243, 'TV_INPUT_HDMI_1'),
  KeyCandidate('HDMI 2', 244, 'TV_INPUT_HDMI_2'),
  KeyCandidate('HDMI 3', 245, 'TV_INPUT_HDMI_3'),
  KeyCandidate('HDMI 4', 246, 'TV_INPUT_HDMI_4'),
  KeyCandidate('Tuner TV', 170, 'TV'),
  KeyCandidate('Peritel / composite', 247, 'TV_INPUT_COMPOSITE_1'),
  KeyCandidate('Menu des contenus', 256, 'TV_CONTENTS_MENU'),
];

const settingsCandidates = <KeyCandidate>[
  KeyCandidate('Reglages', 176, 'SETTINGS'),
  KeyCandidate('Toutes les applis', 284, 'ALL_APPS'),
  KeyCandidate('Menu contextuel', 257, 'TV_MEDIA_CONTEXT_MENU'),
  KeyCandidate('Menu', 82, 'MENU'),
  KeyCandidate('Notifications', 83, 'NOTIFICATION'),
  KeyCandidate('Guide des programmes', 172, 'GUIDE'),
  KeyCandidate('Informations', 165, 'INFO'),
  KeyCandidate('Sous-titres', 175, 'CAPTIONS'),
];

class TvApp {
  final String name;
  final String deepLink;
  final IconData icon;
  final Color color;
  const TvApp(this.name, this.deepLink, this.icon, this.color);
}

const tvApps = <TvApp>[
  TvApp('YouTube', 'https://www.youtube.com', Icons.play_circle_fill,
      Color(0xFFFF0000)),
  TvApp('Netflix', 'https://www.netflix.com/title.*', Icons.movie,
      Color(0xFFE50914)),
  TvApp('Prime Video', 'https://app.primevideo.com', Icons.video_library,
      Color(0xFF00A8E1)),
  TvApp('Disney+', 'https://www.disneyplus.com', Icons.castle,
      Color(0xFF113CCF)),
  TvApp('Molotov', 'https://www.molotov.tv', Icons.live_tv,
      Color(0xFF7B2FF7)),
  TvApp('Spotify', 'https://open.spotify.com', Icons.music_note,
      Color(0xFF1DB954)),
];

// ===========================================================================
// 7. MEMORISATION DU CERTIFICAT ET DES TV APPAIREES
// ===========================================================================

class PairedTv {
  final String host;
  final String name;
  const PairedTv(this.host, this.name);
}

class Store {
  static const _kHosts = 'paired_hosts';

  static Future<ClientIdentity?> loadIdentity(String host) async {
    final prefs = await SharedPreferences.getInstance();
    final cert = prefs.getString('cert_$host');
    final key = prefs.getString('key_$host');
    final modulus = prefs.getString('mod_$host');
    final exponent = prefs.getString('exp_$host');
    if (cert == null || key == null || modulus == null || exponent == null) {
      return null;
    }
    return ClientIdentity(
      certPem: cert,
      keyPem: key,
      modulus: Uint8List.fromList(base64Decode(modulus)),
      exponent: Uint8List.fromList(base64Decode(exponent)),
    );
  }

  static Future<void> saveIdentity(
      String host, String name, ClientIdentity identity) async {
    final prefs = await SharedPreferences.getInstance();
    await prefs.setString('cert_$host', identity.certPem);
    await prefs.setString('key_$host', identity.keyPem);
    await prefs.setString('mod_$host', base64Encode(identity.modulus));
    await prefs.setString('exp_$host', base64Encode(identity.exponent));
    await prefs.setString('name_$host', name);
    final hosts = prefs.getStringList(_kHosts) ?? <String>[];
    if (!hosts.contains(host)) {
      hosts.add(host);
      await prefs.setStringList(_kHosts, hosts);
    }
  }

  static Future<List<PairedTv>> pairedTvs() async {
    final prefs = await SharedPreferences.getInstance();
    final hosts = prefs.getStringList(_kHosts) ?? <String>[];
    return hosts
        .map((h) => PairedTv(h, prefs.getString('name_$h') ?? h))
        .toList();
  }

  static Future<void> forget(String host) async {
    final prefs = await SharedPreferences.getInstance();
    for (final k in ['cert_', 'key_', 'mod_', 'exp_', 'name_']) {
      await prefs.remove('$k$host');
    }
    final hosts = prefs.getStringList(_kHosts) ?? <String>[];
    hosts.remove(host);
    await prefs.setStringList(_kHosts, hosts);
  }
}

// ===========================================================================
// 8. DECOUVERTE DES TV SUR LE RESEAU WIFI
// ===========================================================================

/// Balayage du sous-reseau local : on teste le port 6466 sur chaque adresse.
/// Pas de permission particuliere, contrairement au mDNS sur Android.
class Discovery {
  static Future<String?> localSubnet() async {
    final interfaces = await NetworkInterface.list(
      type: InternetAddressType.IPv4,
      includeLoopback: false,
      includeLinkLocal: false,
    );
    for (final iface in interfaces) {
      for (final addr in iface.addresses) {
        final ip = addr.address;
        if (ip.startsWith('192.168.') ||
            ip.startsWith('10.') ||
            RegExp(r'^172\.(1[6-9]|2\d|3[01])\.').hasMatch(ip)) {
          return ip.substring(0, ip.lastIndexOf('.'));
        }
      }
    }
    return null;
  }

  /// Emet chaque adresse IP qui repond sur le port de la telecommande.
  static Stream<String> scan({
    void Function(double progress)? onProgress,
  }) async* {
    final subnet = await localSubnet();
    if (subnet == null) return;

    const batchSize = 32;
    var done = 0;
    for (var start = 1; start < 255; start += batchSize) {
      final futures = <Future<String?>>[];
      for (var i = start; i < start + batchSize && i < 255; i++) {
        futures.add(_probe('$subnet.$i'));
      }
      final results = await Future.wait(futures);
      done += futures.length;
      onProgress?.call(done / 254);
      for (final host in results) {
        if (host != null) yield host;
      }
    }
  }

  static Future<String?> _probe(String host) async {
    try {
      final socket = await Socket.connect(host, 6466,
          timeout: const Duration(milliseconds: 600));
      socket.destroy();
      return host;
    } catch (_) {
      return null;
    }
  }
}

// ===========================================================================
// 9. INTERFACE
// ===========================================================================

const _bg = Color(0xFF0E1116);
const _surface = Color(0xFF181D25);
const _surfaceHigh = Color(0xFF222935);
const _accent = Color(0xFF4C8DFF);

class RemoteApp extends StatelessWidget {
  const RemoteApp({super.key});

  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      title: 'Telecommande TV',
      debugShowCheckedModeBanner: false,
      theme: ThemeData(
        useMaterial3: true,
        brightness: Brightness.dark,
        scaffoldBackgroundColor: _bg,
        colorScheme: ColorScheme.fromSeed(
          seedColor: _accent,
          brightness: Brightness.dark,
          surface: _surface,
        ),
        fontFamily: 'Roboto',
      ),
      home: const DeviceScreen(),
    );
  }
}

// --- Ecran 1 : choix de la TV ---------------------------------------------

class DeviceScreen extends StatefulWidget {
  const DeviceScreen({super.key});
  @override
  State<DeviceScreen> createState() => _DeviceScreenState();
}

class _DeviceScreenState extends State<DeviceScreen> {
  final List<String> _found = [];
  List<PairedTv> _paired = [];
  bool _scanning = false;
  double _progress = 0;
  StreamSubscription? _scanSub;

  @override
  void initState() {
    super.initState();
    _loadPaired();
    _startScan();
  }

  @override
  void dispose() {
    _scanSub?.cancel();
    super.dispose();
  }

  Future<void> _loadPaired() async {
    final paired = await Store.pairedTvs();
    if (mounted) setState(() => _paired = paired);
  }

  void _startScan() {
    _scanSub?.cancel();
    setState(() {
      _found.clear();
      _scanning = true;
      _progress = 0;
    });
    _scanSub = Discovery.scan(
      onProgress: (p) {
        if (mounted) setState(() => _progress = p);
      },
    ).listen(
      (host) {
        if (mounted && !_found.contains(host)) {
          setState(() => _found.add(host));
        }
      },
      onDone: () {
        if (mounted) setState(() => _scanning = false);
      },
      onError: (_) {
        if (mounted) setState(() => _scanning = false);
      },
    );
  }

  Future<void> _open(String host) async {
    final identity = await Store.loadIdentity(host);
    if (!mounted) return;
    if (identity != null) {
      Navigator.push(
        context,
        MaterialPageRoute(
          builder: (_) => RemoteScreen(host: host, identity: identity),
        ),
      );
    } else {
      final ok = await Navigator.push<bool>(
        context,
        MaterialPageRoute(builder: (_) => PairingScreen(host: host)),
      );
      if (ok == true) {
        await _loadPaired();
        if (mounted) _open(host);
      }
    }
  }

  Future<void> _manualEntry() async {
    final controller = TextEditingController();
    final host = await showDialog<String>(
      context: context,
      builder: (ctx) => AlertDialog(
        backgroundColor: _surface,
        title: const Text('Adresse IP de la TV'),
        content: TextField(
          controller: controller,
          autofocus: true,
          keyboardType: TextInputType.number,
          decoration: const InputDecoration(hintText: '192.168.1.42'),
        ),
        actions: [
          TextButton(
              onPressed: () => Navigator.pop(ctx),
              child: const Text('Annuler')),
          FilledButton(
            onPressed: () => Navigator.pop(ctx, controller.text.trim()),
            child: const Text('Connecter'),
          ),
        ],
      ),
    );
    if (host != null && host.isNotEmpty) _open(host);
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: const Text('Mes televiseurs'),
        backgroundColor: _bg,
        actions: [
          IconButton(
            onPressed: _scanning ? null : _startScan,
            icon: const Icon(Icons.refresh),
            tooltip: 'Rechercher',
          ),
        ],
      ),
      body: ListView(
        padding: const EdgeInsets.all(16),
        children: [
          if (_scanning) ...[
            LinearProgressIndicator(
              value: _progress == 0 ? null : _progress,
              backgroundColor: _surface,
            ),
            const SizedBox(height: 8),
            const Text('Recherche des TV sur le WiFi...',
                style: TextStyle(color: Colors.white54, fontSize: 13)),
            const SizedBox(height: 20),
          ],
          if (_paired.isNotEmpty) ...[
            const _SectionTitle('Deja appairees'),
            ..._paired.map((tv) => _TvTile(
                  title: tv.name,
                  subtitle: tv.host,
                  icon: Icons.tv,
                  trailing: IconButton(
                    icon: const Icon(Icons.link_off, color: Colors.white38),
                    onPressed: () async {
                      await Store.forget(tv.host);
                      _loadPaired();
                    },
                  ),
                  onTap: () => _open(tv.host),
                )),
            const SizedBox(height: 20),
          ],
          const _SectionTitle('Detectees sur le reseau'),
          if (_found.isEmpty && !_scanning)
            const Padding(
              padding: EdgeInsets.symmetric(vertical: 24),
              child: Text(
                "Aucune TV trouvee.\n\nVerifie que la TV est allumee et sur le meme WiFi que le telephone, puis relance la recherche.",
                style: TextStyle(color: Colors.white54, height: 1.5),
              ),
            ),
          ..._found
              .where((h) => !_paired.any((p) => p.host == h))
              .map((host) => _TvTile(
                    title: host,
                    subtitle: 'Appuyer pour appairer',
                    icon: Icons.tv_outlined,
                    onTap: () => _open(host),
                  )),
          const SizedBox(height: 24),
          OutlinedButton.icon(
            onPressed: _manualEntry,
            icon: const Icon(Icons.keyboard),
            label: const Text('Saisir une adresse IP'),
          ),
        ],
      ),
    );
  }
}

class _SectionTitle extends StatelessWidget {
  final String text;
  const _SectionTitle(this.text);
  @override
  Widget build(BuildContext context) => Padding(
        padding: const EdgeInsets.only(bottom: 8),
        child: Text(
          text.toUpperCase(),
          style: const TextStyle(
            color: Colors.white38,
            fontSize: 11,
            letterSpacing: 1.4,
            fontWeight: FontWeight.w600,
          ),
        ),
      );
}

class _TvTile extends StatelessWidget {
  final String title;
  final String subtitle;
  final IconData icon;
  final Widget? trailing;
  final VoidCallback onTap;

  const _TvTile({
    required this.title,
    required this.subtitle,
    required this.icon,
    required this.onTap,
    this.trailing,
  });

  @override
  Widget build(BuildContext context) {
    return Card(
      color: _surface,
      margin: const EdgeInsets.only(bottom: 10),
      child: ListTile(
        leading: Icon(icon, color: _accent),
        title: Text(title),
        subtitle: Text(subtitle,
            style: const TextStyle(color: Colors.white38, fontSize: 12)),
        trailing: trailing,
        onTap: onTap,
      ),
    );
  }
}

// --- Ecran 2 : appairage ---------------------------------------------------

class PairingScreen extends StatefulWidget {
  final String host;
  const PairingScreen({super.key, required this.host});
  @override
  State<PairingScreen> createState() => _PairingScreenState();
}

class _PairingScreenState extends State<PairingScreen> {
  final _codeController = TextEditingController();
  final _nameController = TextEditingController(text: 'Ma TV');

  PairingClient? _client;
  ClientIdentity? _identity;
  String _status = 'Preparation du certificat...';
  bool _waitingForCode = false;
  bool _busy = true;
  String? _error;

  @override
  void initState() {
    super.initState();
    _begin();
  }

  @override
  void dispose() {
    _client?.dispose();
    _codeController.dispose();
    _nameController.dispose();
    super.dispose();
  }

  Future<void> _begin() async {
    setState(() {
      _busy = true;
      _error = null;
      _status = 'Generation du certificat (quelques secondes)...';
    });
    try {
      // La generation RSA est lourde : on la sort du thread graphique.
      final identity = await compute(generateClientIdentity, 'atvremote');
      _identity = identity;

      if (!mounted) return;
      setState(() => _status = 'Connexion a la TV...');

      final client = PairingClient(host: widget.host);
      _client = client;
      await client.start(identity);

      if (!mounted) return;
      setState(() {
        _busy = false;
        _waitingForCode = true;
        _status = 'Un code a 6 caracteres est affiche sur la TV.';
      });
    } catch (e) {
      if (!mounted) return;
      setState(() {
        _busy = false;
        _error = e.toString();
      });
    }
  }

  Future<void> _submitCode() async {
    setState(() {
      _busy = true;
      _error = null;
      _status = 'Verification du code...';
    });
    try {
      await _client!.sendCode(_codeController.text);
      await Store.saveIdentity(
        widget.host,
        _nameController.text.trim().isEmpty
            ? widget.host
            : _nameController.text.trim(),
        _identity!,
      );
      await _client!.dispose();
      if (mounted) Navigator.pop(context, true);
    } catch (e) {
      if (!mounted) return;
      setState(() {
        _busy = false;
        _error = e.toString();
      });
    }
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
          title: Text('Appairage ${widget.host}'), backgroundColor: _bg),
      body: Padding(
        padding: const EdgeInsets.all(24),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.stretch,
          children: [
            const SizedBox(height: 20),
            Icon(_error != null ? Icons.error_outline : Icons.tv,
                size: 64, color: _error != null ? Colors.redAccent : _accent),
            const SizedBox(height: 24),
            Text(
              _error ?? _status,
              textAlign: TextAlign.center,
              style: TextStyle(
                color: _error != null ? Colors.redAccent : Colors.white70,
                height: 1.5,
              ),
            ),
            const SizedBox(height: 32),
            if (_busy) const Center(child: CircularProgressIndicator()),
            if (_waitingForCode && !_busy) ...[
              TextField(
                controller: _codeController,
                autofocus: true,
                textCapitalization: TextCapitalization.characters,
                maxLength: 6,
                textAlign: TextAlign.center,
                style: const TextStyle(
                    fontSize: 32, letterSpacing: 10, fontFamily: 'monospace'),
                inputFormatters: [
                  FilteringTextInputFormatter.allow(RegExp('[0-9a-fA-F]')),
                ],
                decoration: const InputDecoration(
                  hintText: '------',
                  counterText: '',
                  filled: true,
                  fillColor: _surface,
                ),
              ),
              const SizedBox(height: 16),
              TextField(
                controller: _nameController,
                decoration: const InputDecoration(
                  labelText: 'Nom de la TV',
                  filled: true,
                  fillColor: _surface,
                ),
              ),
              const SizedBox(height: 24),
              FilledButton(
                onPressed: _submitCode,
                style: FilledButton.styleFrom(
                    padding: const EdgeInsets.symmetric(vertical: 16)),
                child: const Text('Valider'),
              ),
            ],
            if (_error != null && !_busy) ...[
              const SizedBox(height: 16),
              FilledButton(
                  onPressed: _begin, child: const Text('Reessayer')),
            ],
          ],
        ),
      ),
    );
  }
}

// --- Ecran 3 : la telecommande --------------------------------------------

class RemoteScreen extends StatefulWidget {
  final String host;
  final ClientIdentity identity;
  const RemoteScreen(
      {super.key, required this.host, required this.identity});
  @override
  State<RemoteScreen> createState() => _RemoteScreenState();
}

class _RemoteScreenState extends State<RemoteScreen> {
  late RemoteClient _client;
  String _status = 'Connexion...';
  bool _ready = false;
  bool _showApps = false;

  @override
  void initState() {
    super.initState();
    _client = _newClient();
    _connect();
  }

  @override
  void dispose() {
    _client.dispose();
    super.dispose();
  }

  RemoteClient _newClient() {
    final client = RemoteClient(host: widget.host);
    client.onDisconnected = (_) {
      if (mounted) {
        setState(() {
          _ready = false;
          _status = 'Deconnecte';
        });
      }
    };
    return client;
  }

  Future<void> _connect() async {
    // Une tentative precedente a pu laisser une socket ouverte.
    await _client.dispose();
    _client = _newClient();
    if (!mounted) return;
    setState(() {
      _ready = false;
      _status = 'Connexion...';
    });
    try {
      await _client.connect(widget.identity);
      if (mounted) setState(() => _ready = true);
    } catch (e) {
      if (mounted) {
        setState(() {
          _ready = false;
          _status = e.toString().contains('Handshake')
              ? "Appairage refuse. Supprime la TV de la liste et refais l'appairage."
              : "Connexion impossible : $e";
        });
      }
    }
  }

  void _key(int code) {
    if (!_ready) return;
    HapticFeedback.lightImpact();
    _client.pressKey(code);
  }

  void _tap(int code) {
    if (!_ready) return;
    HapticFeedback.lightImpact();
    _client.tapKey(code);
  }

  /// Propose plusieurs touches pour une meme fonction. La feuille reste
  /// ouverte : on essaie les unes apres les autres en regardant la TV.
  Future<void> _openCandidates(
      String title, List<KeyCandidate> candidates, String footer) async {
    await showModalBottomSheet<void>(
      context: context,
      backgroundColor: _surface,
      showDragHandle: true,
      isScrollControlled: true,
      builder: (ctx) => SafeArea(
        child: Column(
          mainAxisSize: MainAxisSize.min,
          crossAxisAlignment: CrossAxisAlignment.stretch,
          children: [
            Padding(
              padding: const EdgeInsets.fromLTRB(20, 0, 20, 4),
              child: Text(title,
                  style: const TextStyle(
                      fontSize: 18, fontWeight: FontWeight.w600)),
            ),
            const Padding(
              padding: EdgeInsets.fromLTRB(20, 0, 20, 12),
              child: Text(
                'Toutes les TV ne reconnaissent pas les memes touches. '
                'Essaie-les une par une en regardant la TV.',
                style: TextStyle(color: Colors.white54, fontSize: 13),
              ),
            ),
            Flexible(
              child: ListView(
                shrinkWrap: true,
                children: candidates
                    .map((c) => ListTile(
                          dense: true,
                          title: Text(c.label),
                          subtitle: Text('${c.technicalName}  -  ${c.code}',
                              style: const TextStyle(
                                  color: Colors.white38, fontSize: 11)),
                          trailing: const Icon(Icons.send,
                              size: 18, color: _accent),
                          onTap: () => _key(c.code),
                          onLongPress: () {
                            HapticFeedback.mediumImpact();
                            _client.longPressKey(c.code);
                          },
                        ))
                    .toList(),
              ),
            ),
            const Divider(height: 24),
            Padding(
              padding: const EdgeInsets.fromLTRB(20, 0, 20, 8),
              child: Text(footer,
                  style:
                      const TextStyle(color: Colors.white38, fontSize: 12)),
            ),
            Padding(
              padding: const EdgeInsets.fromLTRB(16, 0, 16, 16),
              child: OutlinedButton.icon(
                onPressed: () {
                  Navigator.pop(ctx);
                  Navigator.push(
                    context,
                    MaterialPageRoute(
                      builder: (_) => KeycodeTestScreen(client: _client),
                    ),
                  );
                },
                icon: const Icon(Icons.science_outlined),
                label: const Text("Ecran de test"),
              ),
            ),
          ],
        ),
      ),
    );
  }

  Future<void> _openKeyboard() async {
    final controller = TextEditingController();
    final text = await showDialog<String>(
      context: context,
      builder: (ctx) => AlertDialog(
        backgroundColor: _surface,
        title: const Text('Saisir du texte'),
        content: TextField(
          controller: controller,
          autofocus: true,
          decoration: const InputDecoration(hintText: 'Recherche...'),
        ),
        actions: [
          TextButton(
              onPressed: () => Navigator.pop(ctx),
              child: const Text('Annuler')),
          FilledButton(
            onPressed: () => Navigator.pop(ctx, controller.text),
            child: const Text('Envoyer'),
          ),
        ],
      ),
    );
    if (text != null && text.isNotEmpty) _client.typeText(text);
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        backgroundColor: _bg,
        title: ValueListenableBuilder<String?>(
          valueListenable: _client.currentApp,
          builder: (_, app, __) => Column(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              const Text('Telecommande', style: TextStyle(fontSize: 16)),
              Text(
                _ready ? (app ?? widget.host) : _status,
                style: TextStyle(
                  fontSize: 11,
                  color: _ready ? Colors.greenAccent : Colors.orangeAccent,
                ),
                overflow: TextOverflow.ellipsis,
              ),
            ],
          ),
        ),
        actions: [
          IconButton(
            icon: Icon(_showApps ? Icons.gamepad : Icons.apps),
            onPressed: () => setState(() => _showApps = !_showApps),
          ),
        ],
      ),
      body: !_ready
          ? Center(
              child: Column(
                mainAxisSize: MainAxisSize.min,
                children: [
                  const CircularProgressIndicator(),
                  const SizedBox(height: 24),
                  Padding(
                    padding: const EdgeInsets.symmetric(horizontal: 32),
                    child: Text(_status,
                        textAlign: TextAlign.center,
                        style: const TextStyle(color: Colors.white54)),
                  ),
                  const SizedBox(height: 24),
                  FilledButton(
                      onPressed: _connect, child: const Text('Reessayer')),
                ],
              ),
            )
          : SafeArea(
              child: SingleChildScrollView(
                padding: const EdgeInsets.fromLTRB(20, 8, 20, 24),
                child: _showApps ? _buildApps() : _buildRemote(),
              ),
            ),
    );
  }

  Widget _buildApps() {
    return GridView.count(
      crossAxisCount: 2,
      shrinkWrap: true,
      physics: const NeverScrollableScrollPhysics(),
      mainAxisSpacing: 14,
      crossAxisSpacing: 14,
      childAspectRatio: 1.6,
      children: tvApps
          .map((app) => InkWell(
                onTap: () {
                  HapticFeedback.mediumImpact();
                  _client.launchApp(app.deepLink);
                },
                borderRadius: BorderRadius.circular(18),
                child: Container(
                  decoration: BoxDecoration(
                    color: _surface,
                    borderRadius: BorderRadius.circular(18),
                    border: Border.all(color: app.color.withOpacity(0.35)),
                  ),
                  child: Column(
                    mainAxisAlignment: MainAxisAlignment.center,
                    children: [
                      Icon(app.icon, color: app.color, size: 30),
                      const SizedBox(height: 8),
                      Text(app.name,
                          style: const TextStyle(
                              fontSize: 13, fontWeight: FontWeight.w500)),
                    ],
                  ),
                ),
              ))
          .toList(),
    );
  }

  Widget _buildRemote() {
    return Column(
      children: [
        // Ligne du haut : veille, entrees, clavier
        Row(
          mainAxisAlignment: MainAxisAlignment.spaceEvenly,
          children: [
            _RoundButton(
              icon: Icons.power_settings_new,
              color: const Color(0xFFE5484D),
              onTap: () => _key(KeyCodes.power),
            ),
            _RoundButton(
              icon: Icons.input,
              onTap: () => _openCandidates('Choix de la source',
                  inputCandidates, "Aucune ne marche ? Essaie l'ecran de test."),
            ),
            _RoundButton(icon: Icons.keyboard, onTap: _openKeyboard),
            _RoundButton(
              icon: Icons.settings,
              onTap: () => _openCandidates('Reglages et menus',
                  settingsCandidates, "Aucune ne marche ? Essaie l'ecran de test."),
            ),
          ],
        ),
        const SizedBox(height: 28),

        // Pave directionnel
        _DPad(
          onUp: () => _key(KeyCodes.dpadUp),
          onDown: () => _key(KeyCodes.dpadDown),
          onLeft: () => _key(KeyCodes.dpadLeft),
          onRight: () => _key(KeyCodes.dpadRight),
          onCenter: () => _key(KeyCodes.dpadCenter),
        ),
        const SizedBox(height: 28),

        // Retour, accueil, menu
        Row(
          mainAxisAlignment: MainAxisAlignment.spaceEvenly,
          children: [
            _RoundButton(
                icon: Icons.arrow_back, onTap: () => _key(KeyCodes.back)),
            _RoundButton(
                icon: Icons.home,
                color: _accent,
                onTap: () => _key(KeyCodes.home)),
            _RoundButton(
                icon: Icons.menu, onTap: () => _key(KeyCodes.menu)),
          ],
        ),
        const SizedBox(height: 28),

        // Volume et chaines
        Row(
          children: [
            Expanded(
              child: _Rocker(
                topIcon: Icons.add,
                bottomIcon: Icons.remove,
                label: 'VOL',
                onTop: () => _key(KeyCodes.volumeUp),
                onBottom: () => _key(KeyCodes.volumeDown),
              ),
            ),
            const SizedBox(width: 16),
            Column(
              children: [
                ValueListenableBuilder<VolumeInfo?>(
                  valueListenable: _client.volume,
                  builder: (_, vol, __) => _RoundButton(
                    icon: (vol?.muted ?? false)
                        ? Icons.volume_off
                        : Icons.volume_up,
                    color: (vol?.muted ?? false) ? Colors.orangeAccent : null,
                    onTap: () => _key(KeyCodes.volumeMute),
                  ),
                ),
                const SizedBox(height: 12),
                ValueListenableBuilder<VolumeInfo?>(
                  valueListenable: _client.volume,
                  builder: (_, vol, __) => Text(
                    vol == null ? '--' : '${vol.level}',
                    style: const TextStyle(
                        color: Colors.white38, fontSize: 12),
                  ),
                ),
              ],
            ),
            const SizedBox(width: 16),
            Expanded(
              child: _Rocker(
                topIcon: Icons.keyboard_arrow_up,
                bottomIcon: Icons.keyboard_arrow_down,
                label: 'CH',
                onTop: () => _tap(KeyCodes.channelUp),
                onBottom: () => _tap(KeyCodes.channelDown),
              ),
            ),
          ],
        ),
        const SizedBox(height: 28),

        // Lecture
        Row(
          mainAxisAlignment: MainAxisAlignment.spaceEvenly,
          children: [
            _RoundButton(
                icon: Icons.fast_rewind,
                size: 46,
                onTap: () => _key(KeyCodes.rewind)),
            _RoundButton(
                icon: Icons.skip_previous,
                size: 46,
                onTap: () => _key(KeyCodes.previous)),
            _RoundButton(
                icon: Icons.play_arrow,
                size: 56,
                color: _accent,
                onTap: () => _key(KeyCodes.playPause)),
            _RoundButton(
                icon: Icons.skip_next,
                size: 46,
                onTap: () => _key(KeyCodes.next)),
            _RoundButton(
                icon: Icons.fast_forward,
                size: 46,
                onTap: () => _key(KeyCodes.fastForward)),
          ],
        ),
      ],
    );
  }
}

// --- Ecran 4 : test libre des codes touches ---------------------------------

/// Permet d'envoyer n'importe quel code touche Android et de noter ceux qui
/// marchent, sans avoir a recompiler l'appli a chaque essai.
class KeycodeTestScreen extends StatefulWidget {
  final RemoteClient client;
  const KeycodeTestScreen({super.key, required this.client});
  @override
  State<KeycodeTestScreen> createState() => _KeycodeTestScreenState();
}

class _KeycodeTestScreenState extends State<KeycodeTestScreen> {
  final _controller = TextEditingController();
  final List<String> _log = [];
  String _mode = 'court';

  @override
  void dispose() {
    _controller.dispose();
    super.dispose();
  }

  void _send(int code, [String? label]) {
    switch (_mode) {
      case 'long':
        widget.client.longPressKey(code);
        break;
      case 'unique':
        widget.client.tapKey(code);
        break;
      default:
        widget.client.pressKey(code);
    }
    HapticFeedback.lightImpact();
    setState(() {
      _log.insert(0, '$code${label == null ? '' : '  ($label)'}  -  $_mode');
      if (_log.length > 40) _log.removeLast();
    });
  }

  void _sendTyped() {
    final code = int.tryParse(_controller.text.trim());
    if (code == null || code < 1 || code > 320) {
      ScaffoldMessenger.of(context).showSnackBar(const SnackBar(
        content: Text('Entre un nombre entre 1 et 320'),
      ));
      return;
    }
    _send(code);
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(title: const Text('Test des touches'), backgroundColor: _bg),
      body: SafeArea(
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.stretch,
          children: [
            Padding(
              padding: const EdgeInsets.all(16),
              child: Column(
                crossAxisAlignment: CrossAxisAlignment.stretch,
                children: [
                  const Text(
                    "Envoie n'importe quel code touche Android et regarde la TV. "
                    "Note ceux qui produisent un effet.",
                    style: TextStyle(color: Colors.white54, height: 1.4),
                  ),
                  const SizedBox(height: 16),
                  SegmentedButton<String>(
                    // Libelles courts : trois segments doivent tenir sur un
                    // ecran de telephone sans deborder.
                    segments: const [
                      ButtonSegment(value: 'court', label: Text('Court')),
                      ButtonSegment(value: 'long', label: Text('Long')),
                      ButtonSegment(value: 'unique', label: Text('Seul')),
                    ],
                    selected: {_mode},
                    onSelectionChanged: (s) => setState(() => _mode = s.first),
                  ),
                  const SizedBox(height: 16),
                  Row(
                    children: [
                      Expanded(
                        child: TextField(
                          controller: _controller,
                          keyboardType: TextInputType.number,
                          inputFormatters: [
                            FilteringTextInputFormatter.digitsOnly
                          ],
                          decoration: const InputDecoration(
                            labelText: 'Code touche',
                            hintText: '176',
                            filled: true,
                            fillColor: _surface,
                          ),
                          onSubmitted: (_) => _sendTyped(),
                        ),
                      ),
                      const SizedBox(width: 12),
                      FilledButton(
                        onPressed: _sendTyped,
                        style: FilledButton.styleFrom(
                            padding: const EdgeInsets.symmetric(
                                horizontal: 24, vertical: 18)),
                        child: const Text('Envoyer'),
                      ),
                    ],
                  ),
                ],
              ),
            ),
            const Divider(height: 1),
            Expanded(
              child: ListView(
                padding: const EdgeInsets.symmetric(horizontal: 16),
                children: [
                  const SizedBox(height: 12),
                  const _SectionTitle('Sources et entrees'),
                  _chips(inputCandidates),
                  const SizedBox(height: 20),
                  const _SectionTitle('Reglages et menus'),
                  _chips(settingsCandidates),
                  const SizedBox(height: 20),
                  const _SectionTitle('Envoyees'),
                  if (_log.isEmpty)
                    const Padding(
                      padding: EdgeInsets.symmetric(vertical: 12),
                      child: Text('Rien pour le moment',
                          style:
                              TextStyle(color: Colors.white38, fontSize: 13)),
                    ),
                  ..._log.map((line) => Padding(
                        padding: const EdgeInsets.symmetric(vertical: 3),
                        child: Text(line,
                            style: const TextStyle(
                                color: Colors.white54,
                                fontSize: 12,
                                fontFamily: 'monospace')),
                      )),
                  const SizedBox(height: 24),
                ],
              ),
            ),
          ],
        ),
      ),
    );
  }

  Widget _chips(List<KeyCandidate> candidates) {
    return Wrap(
      spacing: 8,
      runSpacing: 8,
      children: candidates
          .map((c) => ActionChip(
                backgroundColor: _surface,
                label: Text('${c.label}  ${c.code}',
                    style: const TextStyle(fontSize: 12)),
                onPressed: () => _send(c.code, c.technicalName),
              ))
          .toList(),
    );
  }
}

class _RoundButton extends StatelessWidget {
  final IconData icon;
  final VoidCallback onTap;
  final Color? color;
  final double size;

  const _RoundButton({
    required this.icon,
    required this.onTap,
    this.color,
    this.size = 52,
  });

  @override
  Widget build(BuildContext context) {
    return Material(
      color: _surface,
      shape: const CircleBorder(),
      child: InkWell(
        customBorder: const CircleBorder(),
        onTap: onTap,
        child: SizedBox(
          width: size,
          height: size,
          child: Icon(icon, color: color ?? Colors.white70, size: size * 0.45),
        ),
      ),
    );
  }
}

class _Rocker extends StatelessWidget {
  final IconData topIcon;
  final IconData bottomIcon;
  final String label;
  final VoidCallback onTop;
  final VoidCallback onBottom;

  const _Rocker({
    required this.topIcon,
    required this.bottomIcon,
    required this.label,
    required this.onTop,
    required this.onBottom,
  });

  @override
  Widget build(BuildContext context) {
    return Container(
      decoration: BoxDecoration(
        color: _surface,
        borderRadius: BorderRadius.circular(32),
      ),
      child: Column(
        children: [
          _half(topIcon, onTop, true),
          Text(label,
              style: const TextStyle(
                  color: Colors.white38,
                  fontSize: 10,
                  letterSpacing: 1.5,
                  fontWeight: FontWeight.w600)),
          _half(bottomIcon, onBottom, false),
        ],
      ),
    );
  }

  Widget _half(IconData icon, VoidCallback onTap, bool top) {
    return InkWell(
      onTap: onTap,
      borderRadius: BorderRadius.vertical(
        top: top ? const Radius.circular(32) : Radius.zero,
        bottom: top ? Radius.zero : const Radius.circular(32),
      ),
      child: SizedBox(
        height: 54,
        width: double.infinity,
        child: Icon(icon, color: Colors.white70),
      ),
    );
  }
}

/// Pave directionnel circulaire avec un bouton OK au centre.
class _DPad extends StatelessWidget {
  final VoidCallback onUp, onDown, onLeft, onRight, onCenter;

  const _DPad({
    required this.onUp,
    required this.onDown,
    required this.onLeft,
    required this.onRight,
    required this.onCenter,
  });

  @override
  Widget build(BuildContext context) {
    const size = 250.0;
    return SizedBox(
      width: size,
      height: size,
      child: Stack(
        alignment: Alignment.center,
        children: [
          Container(
            decoration: const BoxDecoration(
              color: _surface,
              shape: BoxShape.circle,
            ),
          ),
          Align(
            alignment: Alignment.topCenter,
            child: _arrow(Icons.keyboard_arrow_up, onUp, size),
          ),
          Align(
            alignment: Alignment.bottomCenter,
            child: _arrow(Icons.keyboard_arrow_down, onDown, size),
          ),
          Align(
            alignment: Alignment.centerLeft,
            child: _arrow(Icons.keyboard_arrow_left, onLeft, size),
          ),
          Align(
            alignment: Alignment.centerRight,
            child: _arrow(Icons.keyboard_arrow_right, onRight, size),
          ),
          Material(
            color: _surfaceHigh,
            shape: const CircleBorder(),
            child: InkWell(
              customBorder: const CircleBorder(),
              onTap: onCenter,
              child: const SizedBox(
                width: 96,
                height: 96,
                child: Center(
                  child: Text('OK',
                      style: TextStyle(
                          fontSize: 17,
                          fontWeight: FontWeight.w600,
                          letterSpacing: 1)),
                ),
              ),
            ),
          ),
        ],
      ),
    );
  }

  Widget _arrow(IconData icon, VoidCallback onTap, double size) {
    return InkResponse(
      onTap: onTap,
      radius: 44,
      child: SizedBox(
        width: size * 0.32,
        height: size * 0.32,
        child: Icon(icon, size: 34, color: Colors.white70),
      ),
    );
  }
}
