# Encrypted_Chat_System

> 🌍 Language / 言語: English | 日本語
>
> End-to-end encrypted chat service specification covering identity management, key rotation, secure messaging, and auditability.

## Glossary
- **User**: Person who owns one or more devices and participates in encrypted chats.
- **Device**: Client installation linked to a user that holds local key material.
- **Identity Key**: Long-term Ed25519 key pair that authenticates a user/device.
- **Pre-Key Bundle**: Set of signed pre-keys published to enable session establishment.
- **Session**: Double Ratchet channel established between two devices.
- **Message Envelope**: Transport payload containing ciphertext, metadata, and authentication tag.

## Domain

### User
- **id** (uuid, required) – Unique user identifier
- **displayName** (string, required) – Public profile name
- **devices** (array, required) – Registered devices for the user
- **createdAt** (date, required)
- **updatedAt** (date)

### Device
- **id** (uuid, required)
- **userId** (uuid, required)
- **identityKey** (string, required) – Base64 Encoded Ed25519 public key
- **signedPreKey** (string, required)
- **oneTimePreKeys** (array, required) – Base64 encoded pre-key set
- **lastSeenAt** (date)
- **platform** (string, required) – enum: ios | android | web | desktop

### Session
- **id** (uuid, required)
- **initiatorDeviceId** (uuid, required)
- **responderDeviceId** (uuid, required)
- **rootKey** (string, required)
- **chainKeys** (array, required) – Active Double Ratchet chain keys
- **createdAt** (date, required)
- **state** (string, required) – enum: active | closed | pending

### Message
- **id** (uuid, required)
- **sessionId** (uuid, required)
- **ciphertext** (string, required)
- **authTag** (string, required)
- **sentAt** (date, required)
- **receivedAt** (date)
- **messageType** (string, required) – enum: text | media | control

### AuditLog
- **id** (uuid, required)
- **eventType** (string, required) – enum: device_registered | session_established | message_failed | key_rotated
- **payload** (json, required)
- **createdAt** (date, required)
- **actorId** (uuid)

## Business Rules
1. **BR-SEC-001**: All outbound messages must be encrypted with AES-256-GCM using the active session key before transport.
2. **BR-SEC-002**: Device registrations must publish at least 100 one-time pre-keys; below threshold triggers replenishment.
3. **BR-AUD-001**: AuditLog entries are append-only; updates are forbidden.
4. **BR-PFS-001**: Sessions are rotated after 100 messages or 24 hours, whichever occurs first.
5. **BR-USER-001**: Every User must maintain at least one active Device entry.
6. **BR-DEVICE-001**: Device.identityKey and signedPreKey must be present before Session creation.
7. **BR-SESSION-001**: Active Session records require at least one chain key and both devices to be active.
8. **BR-MSG-001**: Message.authTag must be 16 bytes (Base64 length 24); invalid tags trigger `message_failed` AuditLog entries.
9. **BR-AUD-002**: AuditLog.payload must include an `eventType` field matching the stored eventType.

## State Invariants
- **INV-001**: `Session.state === "active"` implies both devices exist and are not disabled.
- **INV-002**: `Message.receivedAt` cannot be earlier than `Message.sentAt`.
- **INV-003**: Every `AuditLog.actorId` links to an existing `User` or is null for system events.

## Use Cases

### Register Device
- **Actor**: User
- **Preconditions**: Multi-factor authentication succeeds
- **Steps**:
  - Upload identity key, signed pre-key, and pre-key bundle
  - Validate signatures and persist key material
  - Update User.devices with new Device reference
  - Emit `device_registered` AuditLog entry

### Establish Session
- **Actor**: Device → Device communication
- **Preconditions**: Initiator and responder devices are active
- **Steps**:
  - Request responder pre-key bundle
  - Derive shared secrets via X25519 and create root key
  - Persist Session with `state=active` and initial chain keys
  - Notify both clients with delivery receipts

### Send Message
- **Actor**: Device
- **Preconditions**: Session is active
- **Steps**:
  - Derive message key with Double Ratchet
  - Encrypt payload with AES-256-GCM and attach auth tag
  - Persist Message envelope and forward to recipient
  - Receiver acknowledges and advances ratchet

### Rotate Keys
- **Actor**: Scheduler / Device
- **Preconditions**: Rotation threshold reached
- **Steps**:
  - Generate new signed pre-key bundle
  - Publish bundle and retire expired one-time pre-keys
  - Update Device.lastSeenAt and publish rotation status
  - Record `key_rotated` AuditLog entry

## API
- POST /v1/devices - Register new device and publish pre-key bundle.
- POST /v1/sessions - Establish session between devices.
- POST /v1/messages - Submit encrypted message envelope.
- GET /v1/messages/pending - Fetch pending envelopes for device.
- POST /v1/keys/rotate - Trigger pre-key rotation for a device.

## Security Requirements
- **Encryption**: AES-256-GCM for message confidentiality; inputs include ratchet-derived message key and unique nonce.
- **Key Exchange**: X25519 for ECDH; Ed25519 signatures protect pre-key bundles.
- **Integrity**: Auth tags validated before decrypt; invalid tags emit `message_failed` audit event.
- **Forward Secrecy**: Double Ratchet ensures compromise of long-term keys does not reveal historical ciphertext.

## Non-Functional Requirements
- **Availability**: 99.5% monthly uptime for messaging APIs.
- **Latency**: End-to-end message delivery under 500ms within same region.
- **Observability**: AuditLog retention of 180 days with export capability.
- **Compliance**: Aligns with GDPR data retention and deletion requests.

---

## 日本語のサマリ
- すべてのメッセージは Double Ratchet により導出された鍵で AES-256-GCM 暗号化を実施します。
- 端末登録時には identity key・signed pre-key・one-time pre-keys を公開します。
- セッションは 100 メッセージまたは 24 時間ごとに更新され、AuditLog に記録されます。
