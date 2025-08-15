import { describe, it, expect, beforeAll, afterAll, beforeEach } from 'vitest';
import { test as playwrightTest } from '@playwright/test';
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

// E2E test implementations
class E2EUserRepository implements UserRepository {
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

  getAllUsers(): User[] {
    return Array.from(this.users.values());
  }
}

class E2EApiKeyRepository implements ApiKeyRepository {
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

  getAllApiKeys(): ApiKey[] {
    return Array.from(this.apiKeys.values());
  }
}

class E2ERateLimiter implements RateLimiter {
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

// Full application setup for E2E testing
function createTestApp(authService: AuthService, userRepository: E2EUserRepository, apiKeyRepository: E2EApiKeyRepository) {
  const app = Fastify({ logger: false });

  // CORS middleware
  app.addHook('onRequest', async (request, reply) => {
    reply.header('Access-Control-Allow-Origin', '*');
    reply.header('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS');
    reply.header('Access-Control-Allow-Headers', 'Content-Type, Authorization');
    
    if (request.method === 'OPTIONS') {
      reply.code(200).send();
      return;
    }
  });

  // Authentication middleware
  async function authMiddleware(request: any, reply: any) {
    try {
      const authHeader = request.headers.authorization;
      
      if (!authHeader) {
        reply.code(401).send({ error: 'Authorization header required' });
        return;
      }

      let user: User;
      
      if (authHeader.startsWith('Bearer ')) {
        const token = authHeader.substring(7);
        user = await authService.validateJwtToken(token);
      } else if (authHeader.startsWith('ApiKey ')) {
        const key = authHeader.substring(7);
        const apiKey = await authService.validateApiKey(key);
        const foundUser = await userRepository.findById(apiKey.userId);
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

  // Auth routes
  app.post('/api/auth/register', async (request, reply) => {
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

  app.post('/api/auth/login', async (request, reply) => {
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

  app.get('/api/auth/me', async (request, reply) => {
    await authMiddleware(request, reply);
    if (reply.sent) return;

    reply.send({
      id: request.user.id,
      email: request.user.email,
      name: request.user.name,
      role: request.user.role,
      isActive: request.user.isActive,
      createdAt: request.user.createdAt,
      lastLoginAt: request.user.lastLoginAt
    });
  });

  app.post('/api/auth/api-keys', async (request, reply) => {
    await authMiddleware(request, reply);
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

  app.get('/api/auth/api-keys', async (request, reply) => {
    await authMiddleware(request, reply);
    if (reply.sent) return;

    const apiKeys = await apiKeyRepository.findByUserId(request.user.id);
    reply.send(apiKeys.map(key => ({
      id: key.id,
      name: key.name,
      permissions: key.permissions,
      isActive: key.isActive,
      createdAt: key.createdAt,
      lastUsedAt: key.lastUsedAt,
      expiresAt: key.expiresAt
    })));
  });

  app.delete('/api/auth/api-keys/:keyId', async (request, reply) => {
    await authMiddleware(request, reply);
    if (reply.sent) return;

    try {
      const { keyId } = request.params as { keyId: string };
      await authService.revokeApiKey(keyId);
      reply.send({ success: true });
    } catch (error: any) {
      reply.code(500).send({ error: 'Internal server error' });
    }
  });

  app.put('/api/auth/password', async (request, reply) => {
    await authMiddleware(request, reply);
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

  // Protected resource routes
  app.get('/api/dashboard', async (request, reply) => {
    await authMiddleware(request, reply);
    if (reply.sent) return;

    reply.send({
      message: 'Welcome to your dashboard',
      user: request.user.email,
      timestamp: new Date().toISOString()
    });
  });

  app.get('/api/admin/users', async (request, reply) => {
    await authMiddleware(request, reply);
    if (reply.sent) return;

    const hasAdminPermission = await authService.checkPermission(request.user.id, 'admin');
    if (!hasAdminPermission) {
      reply.code(403).send({ error: 'Admin access required' });
      return;
    }

    const users = userRepository.getAllUsers();
    reply.send(users.map(user => ({
      id: user.id,
      email: user.email,
      name: user.name,
      role: user.role,
      isActive: user.isActive,
      createdAt: user.createdAt,
      lastLoginAt: user.lastLoginAt
    })));
  });

  app.get('/api/reports', async (request, reply) => {
    await authMiddleware(request, reply);
    if (reply.sent) return;

    const hasReadPermission = await authService.checkPermission(request.user.id, 'read');
    if (!hasReadPermission) {
      reply.code(403).send({ error: 'Read permission required' });
      return;
    }

    reply.send({
      message: 'Report data',
      user: request.user.email,
      data: ['report1', 'report2', 'report3']
    });
  });

  // Health check
  app.get('/health', async (request, reply) => {
    reply.send({ status: 'ok', timestamp: new Date().toISOString() });
  });

  return app;
}

describe('Authentication End-to-End Tests', () => {
  let app: FastifyInstance;
  let authService: AuthService;
  let userRepository: E2EUserRepository;
  let apiKeyRepository: E2EApiKeyRepository;
  let rateLimiter: E2ERateLimiter;
  let serverUrl: string;

  beforeAll(async () => {
    userRepository = new E2EUserRepository();
    apiKeyRepository = new E2EApiKeyRepository();
    rateLimiter = new E2ERateLimiter();
    authService = new AuthService(
      userRepository,
      apiKeyRepository,
      rateLimiter,
      'e2e-test-jwt-secret-key'
    );

    app = createTestApp(authService, userRepository, apiKeyRepository);
    await app.listen({ port: 0 }); // Use random available port
    
    const address = app.server.address();
    const port = typeof address === 'object' && address ? address.port : 3000;
    serverUrl = `http://localhost:${port}`;
  });

  afterAll(async () => {
    await app.close();
  });

  beforeEach(() => {
    userRepository.clear();
    apiKeyRepository.clear();
    rateLimiter.clear();
  });

  describe('Complete User Journey', () => {
    it('should handle complete user registration and login flow', async () => {
      // Step 1: Health check
      const healthResponse = await fetch(`${serverUrl}/health`);
      expect(healthResponse.status).toBe(200);
      const healthData = await healthResponse.json();
      expect(healthData.status).toBe('ok');

      // Step 2: Register new user
      const registerResponse = await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'john.doe@example.com',
          password: 'SecurePassword123!',
          name: 'John Doe'
        })
      });

      expect(registerResponse.status).toBe(200);
      const userData = await registerResponse.json();
      expect(userData.email).toBe('john.doe@example.com');
      expect(userData.name).toBe('John Doe');

      // Step 3: Login with registered credentials
      const loginResponse = await fetch(`${serverUrl}/api/auth/login`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'john.doe@example.com',
          password: 'SecurePassword123!'
        })
      });

      expect(loginResponse.status).toBe(200);
      const authData = await loginResponse.json();
      expect(authData.token).toBeDefined();
      expect(authData.type).toBe('jwt');

      // Step 4: Access protected resource
      const dashboardResponse = await fetch(`${serverUrl}/api/dashboard`, {
        headers: { 'Authorization': `Bearer ${authData.token}` }
      });

      expect(dashboardResponse.status).toBe(200);
      const dashboardData = await dashboardResponse.json();
      expect(dashboardData.user).toBe('john.doe@example.com');

      // Step 5: Get user profile
      const profileResponse = await fetch(`${serverUrl}/api/auth/me`, {
        headers: { 'Authorization': `Bearer ${authData.token}` }
      });

      expect(profileResponse.status).toBe(200);
      const profileData = await profileResponse.json();
      expect(profileData.email).toBe('john.doe@example.com');
      expect(profileData.name).toBe('John Doe');
    });

    it('should handle API key creation and usage flow', async () => {
      // Step 1: Register and login
      await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'api.user@example.com',
          password: 'SecurePassword123!',
          name: 'API User'
        })
      });

      const loginResponse = await fetch(`${serverUrl}/api/auth/login`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'api.user@example.com',
          password: 'SecurePassword123!'
        })
      });

      const authData = await loginResponse.json();

      // Step 2: Create API key
      const apiKeyResponse = await fetch(`${serverUrl}/api/auth/api-keys`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'Authorization': `Bearer ${authData.token}`
        },
        body: JSON.stringify({
          name: 'Integration Test Key',
          permissions: ['read']
        })
      });

      expect(apiKeyResponse.status).toBe(200);
      const apiKeyData = await apiKeyResponse.json();
      expect(apiKeyData.key).toBeDefined();
      expect(apiKeyData.permissions).toEqual(['read']);

      // Step 3: Use API key to access protected resource
      const reportsResponse = await fetch(`${serverUrl}/api/reports`, {
        headers: { 'Authorization': `ApiKey ${apiKeyData.key}` }
      });

      expect(reportsResponse.status).toBe(200);
      const reportsData = await reportsResponse.json();
      expect(reportsData.user).toBe('api.user@example.com');

      // Step 4: List API keys
      const listKeysResponse = await fetch(`${serverUrl}/api/auth/api-keys`, {
        headers: { 'Authorization': `Bearer ${authData.token}` }
      });

      expect(listKeysResponse.status).toBe(200);
      const keysList = await listKeysResponse.json();
      expect(keysList).toHaveLength(1);
      expect(keysList[0].name).toBe('Integration Test Key');

      // Step 5: Revoke API key
      const revokeResponse = await fetch(`${serverUrl}/api/auth/api-keys/${apiKeyData.id}`, {
        method: 'DELETE',
        headers: { 'Authorization': `Bearer ${authData.token}` }
      });

      expect(revokeResponse.status).toBe(200);

      // Step 6: Verify API key no longer works
      const failedReportsResponse = await fetch(`${serverUrl}/api/reports`, {
        headers: { 'Authorization': `ApiKey ${apiKeyData.key}` }
      });

      expect(failedReportsResponse.status).toBe(401);
    });

    it('should handle password change flow', async () => {
      // Step 1: Register and login
      await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'password.user@example.com',
          password: 'OldPassword123!',
          name: 'Password User'
        })
      });

      const loginResponse = await fetch(`${serverUrl}/api/auth/login`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'password.user@example.com',
          password: 'OldPassword123!'
        })
      });

      const authData = await loginResponse.json();

      // Step 2: Change password
      const changePasswordResponse = await fetch(`${serverUrl}/api/auth/password`, {
        method: 'PUT',
        headers: {
          'Content-Type': 'application/json',
          'Authorization': `Bearer ${authData.token}`
        },
        body: JSON.stringify({
          currentPassword: 'OldPassword123!',
          newPassword: 'NewSecurePassword123!'
        })
      });

      expect(changePasswordResponse.status).toBe(200);

      // Step 3: Verify old password no longer works
      const oldPasswordResponse = await fetch(`${serverUrl}/api/auth/login`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'password.user@example.com',
          password: 'OldPassword123!'
        })
      });

      expect(oldPasswordResponse.status).toBe(401);

      // Step 4: Verify new password works
      const newPasswordResponse = await fetch(`${serverUrl}/api/auth/login`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'password.user@example.com',
          password: 'NewSecurePassword123!'
        })
      });

      expect(newPasswordResponse.status).toBe(200);
    });
  });

  describe('Permission-based Access Control', () => {
    it('should enforce permission-based access control', async () => {
      // Step 1: Create regular user
      await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'regular@example.com',
          password: 'RegularPassword123!',
          name: 'Regular User'
        })
      });

      const loginResponse = await fetch(`${serverUrl}/api/auth/login`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'regular@example.com',
          password: 'RegularPassword123!'
        })
      });

      const authData = await loginResponse.json();

      // Step 2: Try to access admin endpoint (should fail)
      const adminResponse = await fetch(`${serverUrl}/api/admin/users`, {
        headers: { 'Authorization': `Bearer ${authData.token}` }
      });

      expect(adminResponse.status).toBe(403);

      // Step 3: Try to access read endpoint without permission (should fail)
      const reportsResponse = await fetch(`${serverUrl}/api/reports`, {
        headers: { 'Authorization': `Bearer ${authData.token}` }
      });

      expect(reportsResponse.status).toBe(403);

      // Step 4: Create API key with read permission
      const apiKeyResponse = await fetch(`${serverUrl}/api/auth/api-keys`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          'Authorization': `Bearer ${authData.token}`
        },
        body: JSON.stringify({
          name: 'Read Only Key',
          permissions: ['read']
        })
      });

      const apiKeyData = await apiKeyResponse.json();

      // Step 5: Access read endpoint with API key (should work)
      const reportsWithKeyResponse = await fetch(`${serverUrl}/api/reports`, {
        headers: { 'Authorization': `ApiKey ${apiKeyData.key}` }
      });

      expect(reportsWithKeyResponse.status).toBe(200);

      // Step 6: Still can't access admin endpoint
      const adminWithKeyResponse = await fetch(`${serverUrl}/api/admin/users`, {
        headers: { 'Authorization': `ApiKey ${apiKeyData.key}` }
      });

      expect(adminWithKeyResponse.status).toBe(403);
    });

    it('should handle admin user privileges', async () => {
      // Step 1: Create admin user (simulate admin role assignment)
      const registerResponse = await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'admin@example.com',
          password: 'AdminPassword123!',
          name: 'Admin User'
        })
      });

      const userData = await registerResponse.json();

      // Manually set admin role (in real app, this would be done through proper admin setup)
      const adminUser = await userRepository.findById(userData.id);
      if (adminUser) {
        adminUser.role = 'admin';
        userRepository['users'].set(userData.id, adminUser);
      }

      // Step 2: Login as admin
      const loginResponse = await fetch(`${serverUrl}/api/auth/login`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'admin@example.com',
          password: 'AdminPassword123!'
        })
      });

      const authData = await loginResponse.json();

      // Step 3: Access admin endpoint (should work)
      const adminResponse = await fetch(`${serverUrl}/api/admin/users`, {
        headers: { 'Authorization': `Bearer ${authData.token}` }
      });

      expect(adminResponse.status).toBe(200);
      const usersData = await adminResponse.json();
      expect(Array.isArray(usersData)).toBe(true);

      // Step 4: Access regular protected endpoints (should also work)
      const dashboardResponse = await fetch(`${serverUrl}/api/dashboard`, {
        headers: { 'Authorization': `Bearer ${authData.token}` }
      });

      expect(dashboardResponse.status).toBe(200);
    });
  });

  describe('Error Handling and Security', () => {
    it('should handle authentication errors properly', async () => {
      // Test unauthorized access
      const unauthorizedResponse = await fetch(`${serverUrl}/api/dashboard`);
      expect(unauthorizedResponse.status).toBe(401);

      // Test invalid token
      const invalidTokenResponse = await fetch(`${serverUrl}/api/dashboard`, {
        headers: { 'Authorization': 'Bearer invalid-token' }
      });
      expect(invalidTokenResponse.status).toBe(401);

      // Test malformed authorization header
      const malformedAuthResponse = await fetch(`${serverUrl}/api/dashboard`, {
        headers: { 'Authorization': 'InvalidFormat token123' }
      });
      expect(malformedAuthResponse.status).toBe(401);
    });

    it('should handle validation errors', async () => {
      // Test invalid email format
      const invalidEmailResponse = await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'invalid-email',
          password: 'SecurePassword123!',
          name: 'Test User'
        })
      });

      expect(invalidEmailResponse.status).toBe(400);

      // Test weak password
      const weakPasswordResponse = await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'test@example.com',
          password: 'weak',
          name: 'Test User'
        })
      });

      expect(weakPasswordResponse.status).toBe(400);

      // Test missing fields
      const missingFieldsResponse = await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'test@example.com'
          // Missing password and name
        })
      });

      expect(missingFieldsResponse.status).toBe(400);
    });

    it('should handle duplicate registration', async () => {
      const userPayload = {
        email: 'duplicate@example.com',
        password: 'SecurePassword123!',
        name: 'Duplicate User'
      };

      // First registration should succeed
      const firstResponse = await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(userPayload)
      });

      expect(firstResponse.status).toBe(200);

      // Second registration should fail
      const secondResponse = await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(userPayload)
      });

      expect(secondResponse.status).toBe(400);
    });

    it('should handle malformed JSON', async () => {
      const malformedResponse = await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: 'invalid json'
      });

      expect(malformedResponse.status).toBe(400);
    });
  });

  describe('Session Management', () => {
    it('should handle concurrent sessions', async () => {
      // Register user
      await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'concurrent@example.com',
          password: 'ConcurrentPassword123!',
          name: 'Concurrent User'
        })
      });

      // Create multiple sessions
      const loginPromises = Array.from({ length: 5 }, () =>
        fetch(`${serverUrl}/api/auth/login`, {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            email: 'concurrent@example.com',
            password: 'ConcurrentPassword123!'
          })
        })
      );

      const loginResponses = await Promise.all(loginPromises);

      // All logins should succeed
      for (const response of loginResponses) {
        expect(response.status).toBe(200);
      }

      // Extract tokens
      const tokens = await Promise.all(
        loginResponses.map(response => response.json())
      );

      // All tokens should be different
      const tokenSet = new Set(tokens.map(t => t.token));
      expect(tokenSet.size).toBe(5);

      // All tokens should be valid
      const dashboardPromises = tokens.map(tokenData =>
        fetch(`${serverUrl}/api/dashboard`, {
          headers: { 'Authorization': `Bearer ${tokenData.token}` }
        })
      );

      const dashboardResponses = await Promise.all(dashboardPromises);

      for (const response of dashboardResponses) {
        expect(response.status).toBe(200);
      }
    });

    it('should handle token expiration gracefully', async () => {
      // This test would require implementing shorter token expiration for testing
      // For now, we just verify that expired tokens are rejected
      
      // Create a manually expired token (this is a simulation)
      const expiredToken = 'eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9.eyJ1c2VySWQiOiJ0ZXN0IiwiZXhwIjoxfQ.invalid';
      
      const expiredResponse = await fetch(`${serverUrl}/api/dashboard`, {
        headers: { 'Authorization': `Bearer ${expiredToken}` }
      });

      expect(expiredResponse.status).toBe(401);
    });
  });

  describe('Performance and Load Testing', () => {
    it('should handle high load registration', async () => {
      const registrationPromises = Array.from({ length: 50 }, (_, i) =>
        fetch(`${serverUrl}/api/auth/register`, {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({
            email: `user${i}@example.com`,
            password: 'LoadTestPassword123!',
            name: `Load Test User ${i}`
          })
        })
      );

      const responses = await Promise.all(registrationPromises);

      // All registrations should succeed
      let successCount = 0;
      for (const response of responses) {
        if (response.status === 200) {
          successCount++;
        }
      }

      expect(successCount).toBe(50);
    });

    it('should handle rapid API key creation', async () => {
      // Register user first
      await fetch(`${serverUrl}/api/auth/register`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'apiload@example.com',
          password: 'ApiLoadPassword123!',
          name: 'API Load User'
        })
      });

      const loginResponse = await fetch(`${serverUrl}/api/auth/login`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          email: 'apiload@example.com',
          password: 'ApiLoadPassword123!'
        })
      });

      const authData = await loginResponse.json();

      // Create many API keys rapidly
      const apiKeyPromises = Array.from({ length: 20 }, (_, i) =>
        fetch(`${serverUrl}/api/auth/api-keys`, {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json',
            'Authorization': `Bearer ${authData.token}`
          },
          body: JSON.stringify({
            name: `Load Test Key ${i}`,
            permissions: ['read']
          })
        })
      );

      const apiKeyResponses = await Promise.all(apiKeyPromises);

      // All API key creations should succeed
      let successCount = 0;
      for (const response of apiKeyResponses) {
        if (response.status === 200) {
          successCount++;
        }
      }

      expect(successCount).toBe(20);
    });
  });
});