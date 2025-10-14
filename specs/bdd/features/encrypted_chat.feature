Feature: Encrypted chat service conformance readiness
  Background:
    Given a clean encrypted chat service

  Scenario: Device registration publishes enough pre-keys and emits audit log
    Given a user "user-1" with device "device-1"
    When the EncryptedChat service registers device "device-1" with 150 one-time pre-keys
    Then the one-time pre-key bundle should expose at least 100 keys
    And the conformance metrics should report 1 active device
    And the audit log should contain "device_registered"

  Scenario: Invalid auth tag triggers audit violation for AES-GCM envelopes
    Given a user "user-1" with device "device-1"
    And a user "user-2" with device "device-2"
    And an active session "session-1" between devices "device-1" and "device-2"
    When the EncryptedChat service sends a message on session "session-1" with encryption "AES-256-GCM" and auth tag "invalid-auth-tag"
    Then the audit log should contain "message_failed"
    And the conformance metrics should flag invalid auth tags

  Scenario: Session rotation stays within forward secrecy thresholds
    Given a user "user-1" with device "device-1"
    And a user "user-2" with device "device-2"
    And an active session "session-2" between devices "device-1" and "device-2"
    When the EncryptedChat service records 80 messages and 12 elapsed hours on session "session-2"
    Then the session should remain rotation compliant
    And the conformance snapshot should include active chain keys
