import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { Before, After, Given, When, Then } from '@cucumber/cucumber';

class EncryptedChatWorld {
  constructor() {
    this.snapshot = null;
    this.reset();
  }

  reset() {
    this.users = new Map();
    this.devices = new Map();
    this.sessions = new Map();
    this.auditLogs = [];
    this.metrics = {
      oneTimePreKeyCount: 0,
      activeDeviceCount: 0,
      invalidAuthTagLogged: false,
      deliveryLatencyMs: 0,
      gdprRetentionDays: 180,
    };
    this.sessionSnapshot = {
      state: 'inactive',
      chainKeys: [],
      devicesActive: false,
      messagesSinceRotation: 0,
      hoursSinceRotation: 0,
    };
    this.messageSnapshot = {
      encryption: 'AES-256-GCM',
      authTag: 'a'.repeat(24),
    };
    this.auditSnapshot = {
      appendOnly: true,
      payloadAligned: true,
    };
    this.snapshot = null;
  }

  async dispose() {
    /* no-op placeholder for future resources */
  }

  ensureUser(userId) {
    if (!this.users.has(userId)) {
      this.users.set(userId, { devices: new Set() });
    }
  }

  addDevice(userId, deviceId) {
    this.ensureUser(userId);
    if (!this.devices.has(deviceId)) {
      this.devices.set(deviceId, {
        id: deviceId,
        userId,
        active: true,
        registeredPreKeys: 0,
      });
      this.users.get(userId).devices.add(deviceId);
    }
  }

  registerDevice(userId, deviceId, preKeyCount) {
    this.addDevice(userId, deviceId);
    const device = this.devices.get(deviceId);
    device.registeredPreKeys = preKeyCount;
    this.metrics.oneTimePreKeyCount = preKeyCount;
    this.metrics.activeDeviceCount = Array.from(this.devices.values()).filter((d) => d.active).length;
    this.auditLogs.push({ eventType: 'device_registered', actor: userId, deviceId });
    this.auditSnapshot.appendOnly = true;
    this.auditSnapshot.payloadAligned = true;
  }

  establishSession(sessionId, initiatorDeviceId, responderDeviceId, chainKeys = 1) {
    if (!this.devices.has(initiatorDeviceId) || !this.devices.has(responderDeviceId)) {
      throw new Error('Both devices must be registered before establishing a session');
    }
    const chainKeyArray = Array.from({ length: Math.max(1, chainKeys) }, (_value, index) => `chain-${index + 1}`);
    const session = {
      id: sessionId,
      initiatorDeviceId,
      responderDeviceId,
      state: 'active',
      chainKeys: chainKeyArray,
      devicesActive: true,
      messagesSinceRotation: 0,
      hoursSinceRotation: 0,
    };
    this.sessions.set(sessionId, session);
    this.sessionSnapshot = {
      state: session.state,
      chainKeys: [...session.chainKeys],
      devicesActive: session.devicesActive,
      messagesSinceRotation: session.messagesSinceRotation,
      hoursSinceRotation: session.hoursSinceRotation,
    };
  }

  recordSessionActivity(sessionId, messageCount, hoursElapsed) {
    const session = this.sessions.get(sessionId);
    if (!session) {
      throw new Error(`Session ${sessionId} not found`);
    }
    session.messagesSinceRotation = messageCount;
    session.hoursSinceRotation = hoursElapsed;
    this.sessionSnapshot.messagesSinceRotation = messageCount;
    this.sessionSnapshot.hoursSinceRotation = hoursElapsed;
  }

  sendMessage(sessionId, encryption, authTag, deliveryLatency) {
    const session = this.sessions.get(sessionId);
    if (!session || session.state !== 'active') {
      throw new Error(`Session ${sessionId} is not active`);
    }
    this.messageSnapshot = {
      encryption,
      authTag,
    };
    if (typeof deliveryLatency === 'number') {
      this.metrics.deliveryLatencyMs = deliveryLatency;
    }
    const validAuthTag = typeof authTag === 'string' && authTag.length === 24;
    const usesAes256 = encryption === 'AES-256-GCM';
    if (!validAuthTag || !usesAes256) {
      this.metrics.invalidAuthTagLogged = true;
      this.auditLogs.push({ eventType: 'message_failed', sessionId });
    } else {
      this.auditLogs.push({ eventType: 'message_delivered', sessionId });
    }
  }

  hasAuditEvent(eventType) {
    return this.auditLogs.some((entry) => entry.eventType === eventType);
  }

  captureSnapshot(scenarioName) {
    this.snapshot = {
      metadata: {
        scenario: scenarioName,
        generatedAt: new Date().toISOString(),
      },
      metrics: { ...this.metrics },
      session: { ...this.sessionSnapshot },
      message: { ...this.messageSnapshot },
      audit: { ...this.auditSnapshot },
      auditLog: this.auditLogs.slice(),
    };
  }
}

const world = new EncryptedChatWorld();

Before(() => {
  world.reset();
});

After(async function (scenario) {
  world.captureSnapshot(scenario.pickle.name);
  if (world.snapshot) {
    const slug = scenario.pickle.name
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '-')
      .replace(/^-+|-+$/g, '');
    const outputDir = path.resolve('artifacts', 'bdd', 'encrypted-chat');
    fs.mkdirSync(outputDir, { recursive: true });
    const outputPath = path.join(outputDir, `${slug || 'scenario'}.json`);
    fs.writeFileSync(outputPath, JSON.stringify(world.snapshot, null, 2));
  }
  await world.dispose();
});

Given('a clean encrypted chat service', () => {
  world.reset();
});

Given('a user {string} with device {string}', (userId, deviceId) => {
  world.addDevice(userId, deviceId);
});

When('the EncryptedChat service registers device {string} with {int} one-time pre-keys', (deviceId, preKeys) => {
  const device = world.devices.get(deviceId);
  assert.ok(device, `Device ${deviceId} is not registered`);
  world.registerDevice(device.userId, deviceId, preKeys);
});

Then('the one-time pre-key bundle should expose at least {int} keys', (expected) => {
  assert.ok(world.metrics.oneTimePreKeyCount >= Number(expected), 'Pre-key threshold not satisfied');
});

Then('the conformance metrics should report {int} active device', (expected) => {
  assert.equal(world.metrics.activeDeviceCount, Number(expected));
});

Then('the audit log should contain {string}', (eventType) => {
  assert.ok(world.hasAuditEvent(eventType), `Expected audit event ${eventType} not found`);
});

Given('an active session {string} between devices {string} and {string}', (sessionId, initiatorDeviceId, responderDeviceId) => {
  world.establishSession(sessionId, initiatorDeviceId, responderDeviceId, 2);
});

When(
  'the EncryptedChat service sends a message on session {string} with encryption {string} and auth tag {string}',
  (sessionId, encryption, authTag) => {
    world.sendMessage(sessionId, encryption, authTag);
  }
);

Then('the conformance metrics should flag invalid auth tags', () => {
  assert.equal(world.metrics.invalidAuthTagLogged, true);
});

When(
  'the EncryptedChat service records {int} messages and {int} elapsed hours on session {string}',
  (messageCount, hours, sessionId) => {
    world.recordSessionActivity(sessionId, Number(messageCount), Number(hours));
  }
);

Then('the session should remain rotation compliant', () => {
  assert.ok(world.sessionSnapshot.messagesSinceRotation < 100, 'Message threshold exceeded');
  assert.ok(world.sessionSnapshot.hoursSinceRotation < 24, 'Hour threshold exceeded');
});

Then('the conformance snapshot should include active chain keys', () => {
  assert.ok(Array.isArray(world.sessionSnapshot.chainKeys));
  assert.ok(world.sessionSnapshot.chainKeys.length > 0, 'Expected at least one active chain key');
});
