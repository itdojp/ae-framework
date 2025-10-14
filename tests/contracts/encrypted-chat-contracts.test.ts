import { describe, it, expect } from 'vitest';
import { z } from 'zod';

const sampleUuids = {
  user: 'd7e8c1c2-1234-4a56-8b0c-1def23456789',
  device: 'a1b2c3d4-5678-4abc-8def-0123456789ab',
  'device-a': '0f1e2d3c-4567-489a-8bcd-ef0123456789',
  'device-b': '12345678-90ab-4cde-8f01-23456789abcd',
  bundle: 'abcdef01-2345-4abc-8def-0123456789ab',
  session: 'fedcba98-7654-4b32-8a10-1234567890ab',
  'session-2': '76543210-fedc-4b1a-8e90-abcdef123456',
  message: '89abcdef-0123-4bcd-8efa-0123456789ab',
  'message-1': '01234567-89ab-4cde-8f01-abcdef234567'
} as const;

const uuid = (label: keyof typeof sampleUuids) => sampleUuids[label];

const DEVICE_REGISTRATION_CONTRACT = {
  request: {
    method: 'POST',
    path: '/v1/devices',
    body: {
      userId: uuid('user'),
      deviceId: uuid('device'),
      identityKey: 'MCowBQYDK2VwAyEArandomIdentityKey==',
      signedPreKey: 'MCowBQYDK2VwAyEARandomSignedPreKey==',
      oneTimePreKeys: Array.from({ length: 128 }, (_value, index) => `OTPK-${index + 1}`),
      platform: 'ios'
    }
  },
  response: {
    status: 201,
    body: {
      deviceId: uuid('device'),
      status: 'registered',
      publishedPreKeys: 128,
      audit: {
        eventType: 'device_registered',
        actorId: uuid('user'),
        timestamp: '2025-10-14T09:00:00.000Z',
        payloadAligned: true
      }
    }
  }
};

const SESSION_ESTABLISHMENT_CONTRACT = {
  request: {
    method: 'POST',
    path: '/v1/sessions',
    body: {
      initiatorDeviceId: uuid('device-a'),
      responderDeviceId: uuid('device-b'),
      preKeyBundleId: uuid('bundle'),
      rootKey: 'YXV0aF9yb290X2tleQ==',
      chainKeys: Array.from({ length: 2 }, (_value, index) => `chain-key-${index + 1}`)
    }
  },
  response: {
    status: 201,
    body: {
      sessionId: uuid('session'),
      state: 'active',
      chainKeys: Array.from({ length: 2 }, (_value, index) => `chain-key-${index + 1}`),
      devicesActive: true
    }
  }
};

const MESSAGE_ENVELOPE_CONTRACT = {
  request: {
    method: 'POST',
    path: '/v1/messages',
    body: {
      messageId: uuid('message'),
      sessionId: uuid('session'),
      ciphertext: 'base64-ciphertext==',
      authTag: 'A'.repeat(24),
      messageType: 'text',
      sentAt: '2025-10-14T09:05:00.000Z',
      deliveredAt: null
    }
  },
  response: {
    status: 202,
    body: {
      messageId: uuid('message'),
      status: 'queued',
      metrics: {
        deliveryLatencyMs: 320,
        invalidAuthTagLogged: false
      }
    }
  }
};

const PENDING_MESSAGES_CONTRACT = {
  request: {
    method: 'GET',
    path: '/v1/messages/pending',
    query: {
      deviceId: uuid('device-b')
    }
  },
  response: {
    status: 200,
    body: {
      deviceId: uuid('device-b'),
      envelopes: [
        {
          messageId: uuid('message-1'),
          sessionId: uuid('session'),
          ciphertext: 'ciphertext-1==',
          authTag: 'B'.repeat(24),
          messageType: 'text',
          sentAt: '2025-10-14T09:05:00.000Z'
        }
      ]
    }
  }
};

const KEY_ROTATION_CONTRACT = {
  request: {
    method: 'POST',
    path: '/v1/keys/rotate',
    body: {
      deviceId: uuid('device'),
      signedPreKey: 'MCowBQYDK2VwAyEARotatedSignedPreKey==',
      oneTimePreKeys: Array.from({ length: 128 }, (_value, index) => `ROT-KEY-${index + 1}`)
    }
  },
  response: {
    status: 202,
    body: {
      deviceId: uuid('device'),
      status: 'rotation_scheduled',
      audit: {
        eventType: 'key_rotated',
        actorId: uuid('device'),
        timestamp: '2025-10-14T09:10:00.000Z',
        appendOnly: true
      }
    }
  }
};

const deviceRegistrationRequestSchema = z.object({
  userId: z.string().uuid(),
  deviceId: z.string().uuid(),
  identityKey: z.string().min(1),
  signedPreKey: z.string().min(1),
  oneTimePreKeys: z.array(z.string().min(1)).min(100),
  platform: z.enum(['ios', 'android', 'web', 'desktop'])
});

const deviceRegistrationResponseSchema = z.object({
  deviceId: z.string().uuid(),
  status: z.literal('registered'),
  publishedPreKeys: z.number().int().min(100),
  audit: z.object({
    eventType: z.literal('device_registered'),
    actorId: z.string().uuid(),
    timestamp: z.string().datetime(),
    payloadAligned: z.boolean()
  })
});

const sessionRequestSchema = z.object({
  initiatorDeviceId: z.string().uuid(),
  responderDeviceId: z.string().uuid(),
  preKeyBundleId: z.string().uuid(),
  rootKey: z.string().min(1),
  chainKeys: z.array(z.string().min(1)).min(1)
});

const sessionResponseSchema = z.object({
  sessionId: z.string().uuid(),
  state: z.literal('active'),
  chainKeys: z.array(z.string().min(1)).min(1),
  devicesActive: z.boolean()
});

const messageRequestSchema = z.object({
  messageId: z.string().uuid(),
  sessionId: z.string().uuid(),
  ciphertext: z.string().min(1),
  authTag: z.string().length(24),
  messageType: z.enum(['text', 'media', 'control']),
  sentAt: z.string().datetime(),
  deliveredAt: z.string().datetime().nullable()
});

const messageResponseSchema = z.object({
  messageId: z.string().uuid(),
  status: z.enum(['queued', 'delivered']),
  metrics: z.object({
    deliveryLatencyMs: z.number().nonnegative(),
    invalidAuthTagLogged: z.boolean()
  })
});

const pendingResponseSchema = z.object({
  deviceId: z.string().uuid(),
  envelopes: z.array(
    z.object({
      messageId: z.string().uuid(),
      sessionId: z.string().uuid(),
      ciphertext: z.string().min(1),
      authTag: z.string().length(24),
      messageType: z.enum(['text', 'media', 'control']),
      sentAt: z.string().datetime()
    })
  )
});

const rotationRequestSchema = z.object({
  deviceId: z.string().uuid(),
  signedPreKey: z.string().min(1),
  oneTimePreKeys: z.array(z.string().min(1)).min(100)
});

const rotationResponseSchema = z.object({
  deviceId: z.string().uuid(),
  status: z.enum(['rotation_scheduled', 'rotation_complete']),
  audit: z.object({
    eventType: z.literal('key_rotated'),
    actorId: z.string().uuid(),
    timestamp: z.string().datetime(),
    appendOnly: z.boolean()
  })
});

describe('Encrypted chat API contracts', () => {
  it('validates device registration contract', () => {
    expect(deviceRegistrationRequestSchema.parse(DEVICE_REGISTRATION_CONTRACT.request.body)).toBeDefined();
    expect(deviceRegistrationResponseSchema.parse(DEVICE_REGISTRATION_CONTRACT.response.body)).toBeDefined();
  });

  it('validates session establishment contract', () => {
    expect(sessionRequestSchema.parse(SESSION_ESTABLISHMENT_CONTRACT.request.body)).toBeDefined();
    const response = sessionResponseSchema.parse(SESSION_ESTABLISHMENT_CONTRACT.response.body);
    expect(response.chainKeys.length).toBeGreaterThan(0);
  });

  it('validates message envelope contract', () => {
    const request = messageRequestSchema.parse(MESSAGE_ENVELOPE_CONTRACT.request.body);
    expect(request.authTag.length).toBe(24);
    const response = messageResponseSchema.parse(MESSAGE_ENVELOPE_CONTRACT.response.body);
    expect(response.metrics.invalidAuthTagLogged).toBe(false);
  });

  it('validates pending message retrieval contract', () => {
    const response = pendingResponseSchema.parse(PENDING_MESSAGES_CONTRACT.response.body);
    expect(response.envelopes.length).toBeGreaterThan(0);
  });

  it('validates key rotation contract', () => {
    expect(rotationRequestSchema.parse(KEY_ROTATION_CONTRACT.request.body)).toBeDefined();
    expect(rotationResponseSchema.parse(KEY_ROTATION_CONTRACT.response.body)).toBeDefined();
  });
});
