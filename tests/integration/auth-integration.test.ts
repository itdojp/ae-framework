import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import Fastify, { FastifyInstance } from 'fastify';
import {
  AuthService,
  User,
  ApiKey,
  UserRepository,
  ApiKeyRepository,
  RateLimiter,
  AuthenticationError,
  ValidationError
} from '../../src/services/auth-service.js';

// Simple in-memory implementations for integration testing
class InMemoryUserRepository implements UserRepository {
  private users: Map<string, User> = new Map();
  private emailIndex: Map<string, string> = new Map();

  async findByEmail(email: string): Promise<User | null> {
    const userId = this.emailIndex.get(email);
    return userId ? this.users.get(userId) || null : null;
  }

  async findById(id: string): Promise<User | null> {
    return this.users.get(id) || null;
  }

  async create(user: Omit<User, 'id' | 'createdAt'>): Promise<User> {
    const newUser: User = {
      id: `user-${Date.now()}-${Math.random()}`,
      createdAt: new Date(),
      ...user
    };
    this.users.set(newUser.id, newUser);
    this.emailIndex.set(newUser.email, newUser.id);
    return newUser;
  }

  async updateLastLogin(userId: string): Promise<void> {
    const user = this.users.get(userId);
    if (user) {
      user.lastLoginAt = new Date();
    }
  }

  async updatePassword(userId: string, passwordHash: string): Promise<void> {
    const user = this.users.get(userId);
    if (user) {
      user.passwordHash = passwordHash;
    }
  }

  clear(): void {
    this.users.clear();
    this.emailIndex.clear();
  }
}

class InMemoryApiKeyRepository implements ApiKeyRepository {
  private apiKeys: Map<string, ApiKey> = new Map();
  private keyIndex: Map<string, string> = new Map();

  async findByKey(hashedKey: string): Promise<ApiKey | null> {
    const keyId = this.keyIndex.get(hashedKey);
    return keyId ? this.apiKeys.get(keyId) || null : null;
  }

  async findByUserId(userId: string): Promise<ApiKey[]> {
    return Array.from(this.apiKeys.values()).filter(key => key.userId === userId);
  }

  async create(apiKey: Omit<ApiKey, 'id' | 'createdAt'>): Promise<ApiKey> {
    const newApiKey: ApiKey = {
      id: `key-${Date.now()}-${Math.random()}`,
      createdAt: new Date(),
      ...apiKey
    };
    this.apiKeys.set(newApiKey.id, newApiKey);
    this.keyIndex.set(newApiKey.hashedKey, newApiKey.id);
    return newApiKey;
  }

  async updateLastUsed(keyId: string): Promise<void> {
    const apiKey = this.apiKeys.get(keyId);
    if (apiKey) {
      apiKey.lastUsedAt = new Date();
    }
  }

  async revoke(keyId: string): Promise<void> {
    const apiKey = this.apiKeys.get(keyId);
    if (apiKey) {
      apiKey.isActive = false;
    }
  }

  clear(): void {
    this.apiKeys.clear();
    this.keyIndex.clear();
  }
}

class InMemoryRateLimiter implements RateLimiter {
  private attempts: Map<string, { count: number; firstAttempt: Date }> = new Map();
  private maxAttempts = 5;
  private windowMs = 15 * 60 * 1000; // 15 minutes

  async checkLimit(identifier: string, operation: string): Promise<boolean> {
    const key = `${identifier}:${operation}`;
    const now = new Date();
    const record = this.attempts.get(key);

    if (!record) {
      this.attempts.set(key, { count: 1, firstAttempt: now });
      return true;
    }

    // Reset if window has passed
    if (now.getTime() - record.firstAttempt.getTime() > this.windowMs) {
      this.attempts.set(key, { count: 1, firstAttempt: now });
      return true;
    }

    record.count++;
    return record.count <= this.maxAttempts;
  }

  async getRemainingAttempts(identifier: string, operation: string): Promise<number> {
    const key = `${identifier}:${operation}`;
    const record = this.attempts.get(key);
    
    if (!record) return this.maxAttempts;
    
    const now = new Date();
    if (now.getTime() - record.firstAttempt.getTime() > this.windowMs) {
      return this.maxAttempts;
    }

    return Math.max(0, this.maxAttempts - record.count);
  }

  clear(): void {
    this.attempts.clear();
  }
}

// Authentication middleware for Fastify
async function authMiddleware(request: any, reply: any, authService: AuthService) {
  try {
    const authHeader = request.headers.authorization;
    
    if (!authHeader) {
      reply.code(401).send({ error: 'Authorization header required' });
      return;
    }

    let user: User;
    
    if (authHeader.startsWith('Bearer ')) {
      // JWT token
      const token = authHeader.substring(7);
      user = await authService.validateJwtToken(token);
    } else if (authHeader.startsWith('ApiKey ')) {
      // API Key
      const key = authHeader.substring(7);
      const apiKey = await authService.validateApiKey(key);
      const foundUser = await authService['userRepository'].findById(apiKey.userId);
      if (!foundUser) {
        reply.code(401).send({ error: 'Invalid API key' });
        return;
      }
      user = foundUser;
    } else {
      reply.code(401).send({ error: 'Invalid authorization format' });
      return;
    }

    request.user = user;
  } catch (error) {
    reply.code(401).send({ error: 'Invalid credentials' });
  }
}

// Permission middleware
function requirePermission(permission: string) {
  return async function(request: any, reply: any, authService: AuthService) {
    if (!request.user) {
      reply.code(401).send({ error: 'Authentication required' });
      return;
    }

    const hasPermission = await authService.checkPermission(request.user.id, permission);
    if (!hasPermission) {
      reply.code(403).send({ error: 'Insufficient permissions' });
      return;
    }
  };
}

describe('Authentication Integration Tests', () => {
  let app: FastifyInstance;
  let authService: AuthService;
  let userRepository: InMemoryUserRepository;
  let apiKeyRepository: InMemoryApiKeyRepository;
  let rateLimiter: InMemoryRateLimiter;

  beforeEach(async () => {
    userRepository = new InMemoryUserRepository();
    apiKeyRepository = new InMemoryApiKeyRepository();
    rateLimiter = new InMemoryRateLimiter();
    authService = new AuthService(
      userRepository,
      apiKeyRepository,
      rateLimiter,
      'integration-test-jwt-secret-key'
    );

    app = Fastify({ logger: false });

    // Register authentication routes
    app.post('/auth/register', async (request, reply) => {
      try {
        const user = await authService.register(request.body as any);
        reply.send({
          id: user.id,
          email: user.email,
          name: user.name,
          role: user.role,
          isActive: user.isActive,
          createdAt: user.createdAt
        });
      } catch (error: any) {
        if (error instanceof ValidationError) {
          reply.code(400).send({ error: error.message });
        } else {
          reply.code(500).send({ error: 'Internal server error' });
        }
      }
    });

    app.post('/auth/login', async (request, reply) => {
      try {
        const authToken = await authService.login(request.body as any);
        reply.send(authToken);
      } catch (error: any) {
        if (error instanceof ValidationError) {
          reply.code(400).send({ error: error.message });
        } else if (error instanceof AuthenticationError) {
          reply.code(401).send({ error: error.message });
        } else {
          reply.code(500).send({ error: 'Internal server error' });
        }
      }
    });

    app.post('/auth/api-keys', async (request, reply) => {
      await authMiddleware(request, reply, authService);
      if (reply.sent) return;

      try {
        const apiKey = await authService.createApiKey(request.user.id, request.body as any);
        reply.send(apiKey);
      } catch (error: any) {
        if (error instanceof ValidationError) {
          reply.code(400).send({ error: error.message });
        } else {
          reply.code(500).send({ error: 'Internal server error' });
        }
      }
    });

    app.delete('/auth/api-keys/:keyId', async (request, reply) => {
      await authMiddleware(request, reply, authService);
      if (reply.sent) return;

      try {
        const { keyId } = request.params as { keyId: string };
        await authService.revokeApiKey(keyId);
        reply.send({ success: true });
      } catch (error: any) {
        reply.code(500).send({ error: 'Internal server error' });
      }
    });

    app.put('/auth/password', async (request, reply) => {
      await authMiddleware(request, reply, authService);
      if (reply.sent) return;

      try {
        const { currentPassword, newPassword } = request.body as any;
        await authService.changePassword(request.user.id, currentPassword, newPassword);
        reply.send({ success: true });
      } catch (error: any) {
        if (error instanceof ValidationError || error instanceof AuthenticationError) {
          reply.code(400).send({ error: error.message });
        } else {
          reply.code(500).send({ error: 'Internal server error' });
        }
      }
    });

    // Protected routes for testing authorization
    app.get('/api/public', async (request, reply) => {
      reply.send({ message: 'This is a public endpoint' });
    });

    app.get('/api/protected', async (request, reply) => {
      await authMiddleware(request, reply, authService);
      if (reply.sent) return;

      reply.send({ message: 'This is a protected endpoint', user: request.user.email });
    });

    app.get('/api/admin', async (request, reply) => {
      await authMiddleware(request, reply, authService);
      if (reply.sent) return;

      await requirePermission('admin')(request, reply, authService);
      if (reply.sent) return;

      reply.send({ message: 'This is an admin endpoint', user: request.user.email });
    });

    app.get('/api/read-only', async (request, reply) => {
      await authMiddleware(request, reply, authService);
      if (reply.sent) return;

      await requirePermission('read')(request, reply, authService);
      if (reply.sent) return;

      reply.send({ message: 'This is a read-only endpoint', user: request.user.email });
    });

    await app.ready();
  });

  afterEach(async () => {
    await app.close();
    userRepository.clear();
    apiKeyRepository.clear();
    rateLimiter.clear();
  });

  describe('User Registration and Login Flow', () => {
    it('should complete full registration and login flow', async () => {
      // Register a new user
      const registerResponse = await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecurePass123!',
          name: 'Test User'
        }
      });

      expect(registerResponse.statusCode).toBe(200);
      const user = JSON.parse(registerResponse.payload);
      expect(user.email).toBe('test@example.com');
      expect(user.name).toBe('Test User');
      expect(user.role).toBe('user');

      // Login with the registered user
      const loginResponse = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'SecurePass123!'
        }
      });

      expect(loginResponse.statusCode).toBe(200);
      const authToken = JSON.parse(loginResponse.payload);
      expect(authToken.token).toBeDefined();
      expect(authToken.type).toBe('jwt');
      expect(authToken.user.email).toBe('test@example.com');
    });

    it('should reject duplicate user registration', async () => {
      const userPayload = {
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      };

      // First registration should succeed
      const firstResponse = await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: userPayload
      });
      expect(firstResponse.statusCode).toBe(200);

      // Second registration should fail
      const secondResponse = await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: userPayload
      });
      expect(secondResponse.statusCode).toBe(400);
    });

    it('should reject login with invalid credentials', async () => {
      // Register user first
      await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecurePass123!',
          name: 'Test User'
        }
      });

      // Try to login with wrong password
      const response = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'WrongPassword123!'
        }
      });

      expect(response.statusCode).toBe(401);
    });
  });

  describe('JWT Authentication Flow', () => {
    let authToken: string;

    beforeEach(async () => {
      // Register and login to get a token
      await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecurePass123!',
          name: 'Test User'
        }
      });

      const loginResponse = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'SecurePass123!'
        }
      });

      const loginData = JSON.parse(loginResponse.payload);
      authToken = loginData.token;
    });

    it('should access protected endpoints with valid JWT', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/protected',
        headers: {
          authorization: `Bearer ${authToken}`
        }
      });

      expect(response.statusCode).toBe(200);
      const data = JSON.parse(response.payload);
      expect(data.message).toBe('This is a protected endpoint');
      expect(data.user).toBe('test@example.com');
    });

    it('should reject access to protected endpoints without token', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/protected'
      });

      expect(response.statusCode).toBe(401);
    });

    it('should reject access with invalid JWT', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/protected',
        headers: {
          authorization: 'Bearer invalid-token'
        }
      });

      expect(response.statusCode).toBe(401);
    });

    it('should allow access to public endpoints without token', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/public'
      });

      expect(response.statusCode).toBe(200);
      const data = JSON.parse(response.payload);
      expect(data.message).toBe('This is a public endpoint');
    });
  });

  describe('API Key Authentication Flow', () => {
    let authToken: string;
    let apiKey: string;
    let userId: string;

    beforeEach(async () => {
      // Register and login to get a token
      const registerResponse = await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecurePass123!',
          name: 'Test User'
        }
      });
      userId = JSON.parse(registerResponse.payload).id;

      const loginResponse = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'SecurePass123!'
        }
      });

      const loginData = JSON.parse(loginResponse.payload);
      authToken = loginData.token;

      // Create an API key
      const apiKeyResponse = await app.inject({
        method: 'POST',
        url: '/auth/api-keys',
        headers: {
          authorization: `Bearer ${authToken}`
        },
        payload: {
          name: 'Test API Key',
          permissions: ['read']
        }
      });

      const apiKeyData = JSON.parse(apiKeyResponse.payload);
      apiKey = apiKeyData.key;
    });

    it('should create API key with valid JWT', async () => {
      const response = await app.inject({
        method: 'POST',
        url: '/auth/api-keys',
        headers: {
          authorization: `Bearer ${authToken}`
        },
        payload: {
          name: 'Another Test Key',
          permissions: ['read', 'write']
        }
      });

      expect(response.statusCode).toBe(200);
      const data = JSON.parse(response.payload);
      expect(data.name).toBe('Another Test Key');
      expect(data.permissions).toEqual(['read', 'write']);
      expect(data.key).toBeDefined();
    });

    it('should access protected endpoints with valid API key', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/protected',
        headers: {
          authorization: `ApiKey ${apiKey}`
        }
      });

      expect(response.statusCode).toBe(200);
      const data = JSON.parse(response.payload);
      expect(data.message).toBe('This is a protected endpoint');
      expect(data.user).toBe('test@example.com');
    });

    it('should enforce permissions with API key', async () => {
      // Try to access read-only endpoint (should work)
      const readResponse = await app.inject({
        method: 'GET',
        url: '/api/read-only',
        headers: {
          authorization: `ApiKey ${apiKey}`
        }
      });

      expect(readResponse.statusCode).toBe(200);

      // Try to access admin endpoint (should fail)
      const adminResponse = await app.inject({
        method: 'GET',
        url: '/api/admin',
        headers: {
          authorization: `ApiKey ${apiKey}`
        }
      });

      expect(adminResponse.statusCode).toBe(403);
    });

    it('should revoke API keys', async () => {
      // Get the API key ID (in a real implementation, you'd have a list endpoint)
      const keys = await apiKeyRepository.findByUserId(userId);
      const keyId = keys[0].id;

      // Revoke the key
      const revokeResponse = await app.inject({
        method: 'DELETE',
        url: `/auth/api-keys/${keyId}`,
        headers: {
          authorization: `Bearer ${authToken}`
        }
      });

      expect(revokeResponse.statusCode).toBe(200);

      // Try to use the revoked key
      const response = await app.inject({
        method: 'GET',
        url: '/api/protected',
        headers: {
          authorization: `ApiKey ${apiKey}`
        }
      });

      expect(response.statusCode).toBe(401);
    });
  });

  describe('Permission-based Access Control', () => {
    let adminToken: string;
    let userToken: string;
    let readApiKey: string;

    beforeEach(async () => {
      // Create admin user
      const adminRegisterResponse = await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'admin@example.com',
          password: 'AdminPass123!',
          name: 'Admin User'
        }
      });
      const adminUser = JSON.parse(adminRegisterResponse.payload);

      // Set admin role manually (in real app, this would be done through proper admin setup)
      const foundAdminUser = await userRepository.findById(adminUser.id);
      if (foundAdminUser) {
        foundAdminUser.role = 'admin';
        userRepository['users'].set(adminUser.id, foundAdminUser);
      }

      const adminLoginResponse = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'admin@example.com',
          password: 'AdminPass123!'
        }
      });
      adminToken = JSON.parse(adminLoginResponse.payload).token;

      // Create regular user
      const userRegisterResponse = await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'user@example.com',
          password: 'UserPass123!',
          name: 'Regular User'
        }
      });
      const regularUser = JSON.parse(userRegisterResponse.payload);

      const userLoginResponse = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'user@example.com',
          password: 'UserPass123!'
        }
      });
      userToken = JSON.parse(userLoginResponse.payload).token;

      // Create read-only API key for regular user
      const apiKeyResponse = await app.inject({
        method: 'POST',
        url: '/auth/api-keys',
        headers: {
          authorization: `Bearer ${userToken}`
        },
        payload: {
          name: 'Read Only Key',
          permissions: ['read']
        }
      });
      readApiKey = JSON.parse(apiKeyResponse.payload).key;
    });

    it('should allow admin access to admin endpoints', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/admin',
        headers: {
          authorization: `Bearer ${adminToken}`
        }
      });

      expect(response.statusCode).toBe(200);
    });

    it('should deny regular user access to admin endpoints', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/admin',
        headers: {
          authorization: `Bearer ${userToken}`
        }
      });

      expect(response.statusCode).toBe(403);
    });

    it('should allow API key access based on permissions', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/read-only',
        headers: {
          authorization: `ApiKey ${readApiKey}`
        }
      });

      expect(response.statusCode).toBe(200);
    });

    it('should deny API key access without proper permissions', async () => {
      const response = await app.inject({
        method: 'GET',
        url: '/api/admin',
        headers: {
          authorization: `ApiKey ${readApiKey}`
        }
      });

      expect(response.statusCode).toBe(403);
    });
  });

  describe('Password Change Flow', () => {
    let authToken: string;

    beforeEach(async () => {
      await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'OriginalPass123!',
          name: 'Test User'
        }
      });

      const loginResponse = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'OriginalPass123!'
        }
      });

      authToken = JSON.parse(loginResponse.payload).token;
    });

    it('should change password with valid current password', async () => {
      const changeResponse = await app.inject({
        method: 'PUT',
        url: '/auth/password',
        headers: {
          authorization: `Bearer ${authToken}`
        },
        payload: {
          currentPassword: 'OriginalPass123!',
          newPassword: 'NewSecurePass123!'
        }
      });

      expect(changeResponse.statusCode).toBe(200);

      // Verify old password no longer works
      const oldLoginResponse = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'OriginalPass123!'
        }
      });

      expect(oldLoginResponse.statusCode).toBe(401);

      // Verify new password works
      const newLoginResponse = await app.inject({
        method: 'POST',
        url: '/auth/login',
        payload: {
          email: 'test@example.com',
          password: 'NewSecurePass123!'
        }
      });

      expect(newLoginResponse.statusCode).toBe(200);
    });

    it('should reject password change with wrong current password', async () => {
      const response = await app.inject({
        method: 'PUT',
        url: '/auth/password',
        headers: {
          authorization: `Bearer ${authToken}`
        },
        payload: {
          currentPassword: 'WrongPassword123!',
          newPassword: 'NewSecurePass123!'
        }
      });

      expect(response.statusCode).toBe(400);
    });

    it('should reject password change with weak new password', async () => {
      const response = await app.inject({
        method: 'PUT',
        url: '/auth/password',
        headers: {
          authorization: `Bearer ${authToken}`
        },
        payload: {
          currentPassword: 'OriginalPass123!',
          newPassword: 'weak'
        }
      });

      expect(response.statusCode).toBe(400);
    });
  });

  describe('Error Handling and Edge Cases', () => {
    it('should handle malformed JSON gracefully', async () => {
      const response = await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: 'invalid json',
        headers: {
          'content-type': 'application/json'
        }
      });

      expect(response.statusCode).toBe(400);
    });

    it('should handle missing required fields', async () => {
      const response = await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com'
          // Missing password and name
        }
      });

      expect(response.statusCode).toBe(400);
    });

    it('should handle concurrent requests properly', async () => {
      // Register a user first
      await app.inject({
        method: 'POST',
        url: '/auth/register',
        payload: {
          email: 'test@example.com',
          password: 'SecurePass123!',
          name: 'Test User'
        }
      });

      // Make multiple concurrent login requests
      const promises = Array.from({ length: 10 }, () =>
        app.inject({
          method: 'POST',
          url: '/auth/login',
          payload: {
            email: 'test@example.com',
            password: 'SecurePass123!'
          }
        })
      );

      const responses = await Promise.all(promises);

      // All requests should succeed
      responses.forEach(response => {
        expect(response.statusCode).toBe(200);
      });

      // All tokens should be different (due to timestamp in JWT)
      const tokens = responses.map(r => JSON.parse(r.payload).token);
      const uniqueTokens = new Set(tokens);
      expect(uniqueTokens.size).toBe(tokens.length);
    });
  });
});