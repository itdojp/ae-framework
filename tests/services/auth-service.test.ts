import { describe, it, expect, beforeEach, vi } from 'vitest';
import * as crypto from 'crypto';
import {
  AuthService,
  AuthenticationError,
  AuthorizationError,
  ValidationError,
  RateLimitError,
  User,
  ApiKey,
  UserRepository,
  ApiKeyRepository,
  RateLimiter,
  LoginRequest,
  RegisterRequest,
  ApiKeyRequest
} from '../../src/services/auth-service.js';

// Test doubles - same as in security tests but focusing on unit behavior
class MockUserRepository implements UserRepository {
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
      id: crypto.randomUUID(),
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

  addUser(user: User): void {
    this.users.set(user.id, user);
    this.emailIndex.set(user.email, user.id);
  }

  clear(): void {
    this.users.clear();
    this.emailIndex.clear();
  }
}

class MockApiKeyRepository implements ApiKeyRepository {
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
      id: crypto.randomUUID(),
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

class MockRateLimiter implements RateLimiter {
  private shouldAllow = true;
  private remainingAttempts = 5;

  async checkLimit(identifier: string, operation: string): Promise<boolean> {
    return this.shouldAllow;
  }

  async getRemainingAttempts(identifier: string, operation: string): Promise<number> {
    return this.remainingAttempts;
  }

  setAllowAttempts(allow: boolean): void {
    this.shouldAllow = allow;
  }

  setRemainingAttempts(remaining: number): void {
    this.remainingAttempts = remaining;
  }
}

describe('AuthService Unit Tests', () => {
  let authService: AuthService;
  let userRepository: MockUserRepository;
  let apiKeyRepository: MockApiKeyRepository;
  let rateLimiter: MockRateLimiter;

  beforeEach(() => {
    userRepository = new MockUserRepository();
    apiKeyRepository = new MockApiKeyRepository();
    rateLimiter = new MockRateLimiter();
    authService = new AuthService(
      userRepository,
      apiKeyRepository,
      rateLimiter,
      'test-jwt-secret-key-for-unit-tests'
    );
  });

  describe('User Registration', () => {
    it('should successfully register a valid user', async () => {
      const registerRequest: RegisterRequest = {
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      };

      const user = await authService.register(registerRequest);

      expect(user).toBeDefined();
      expect(user.id).toBeDefined();
      expect(user.email).toBe(registerRequest.email);
      expect(user.name).toBe(registerRequest.name);
      expect(user.role).toBe('user');
      expect(user.isActive).toBe(true);
      expect(user.createdAt).toBeInstanceOf(Date);
      expect(user.passwordHash).not.toBe(registerRequest.password);
    });

    it('should reject registration with invalid email format', async () => {
      const invalidEmails = [
        'invalid-email',
        '@example.com',
        'test@',
        'test.example.com'
      ];

      for (const email of invalidEmails) {
        await expect(authService.register({
          email,
          password: 'SecurePass123!',
          name: 'Test User'
        })).rejects.toThrow(ValidationError);
      }
    });

    it('should reject registration with weak password', async () => {
      await expect(authService.register({
        email: 'test@example.com',
        password: 'weak',
        name: 'Test User'
      })).rejects.toThrow(ValidationError);
    });

    it('should reject registration if user already exists', async () => {
      const registerRequest: RegisterRequest = {
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      };

      await authService.register(registerRequest);

      await expect(authService.register(registerRequest))
        .rejects.toThrow(ValidationError);
    });

    it('should validate required fields', async () => {
      const incompleteRequests = [
        { email: '', password: 'SecurePass123!', name: 'Test User' },
        { email: 'test@example.com', password: '', name: 'Test User' },
        { email: 'test@example.com', password: 'SecurePass123!', name: '' }
      ];

      for (const request of incompleteRequests) {
        await expect(authService.register(request as RegisterRequest))
          .rejects.toThrow(ValidationError);
      }
    });
  });

  describe('User Authentication', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
    });

    it('should successfully authenticate valid credentials', async () => {
      const loginRequest: LoginRequest = {
        email: 'test@example.com',
        password: 'TestPass123!'
      };

      const authToken = await authService.login(loginRequest);

      expect(authToken).toBeDefined();
      expect(authToken.token).toBeDefined();
      expect(authToken.type).toBe('jwt');
      expect(authToken.expiresAt).toBeInstanceOf(Date);
      expect(authToken.user.id).toBe(testUser.id);
      expect(authToken.user.email).toBe(testUser.email);
    });

    it('should reject authentication with invalid password', async () => {
      await expect(authService.login({
        email: 'test@example.com',
        password: 'WrongPassword123!'
      })).rejects.toThrow(AuthenticationError);
    });

    it('should reject authentication with non-existent email', async () => {
      await expect(authService.login({
        email: 'nonexistent@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow(AuthenticationError);
    });

    it('should reject authentication for inactive users', async () => {
      testUser.isActive = false;
      userRepository.addUser(testUser);

      await expect(authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow(AuthenticationError);
    });

    it('should respect rate limiting', async () => {
      rateLimiter.setAllowAttempts(false);

      await expect(authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow(RateLimitError);
    });

    it('should update last login timestamp on successful authentication', async () => {
      expect(testUser.lastLoginAt).toBeUndefined();

      await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      const updatedUser = await userRepository.findById(testUser.id);
      expect(updatedUser?.lastLoginAt).toBeInstanceOf(Date);
    });

    it('should validate login request format', async () => {
      const invalidRequests = [
        { email: 'invalid-email', password: 'TestPass123!' },
        { email: 'test@example.com', password: 'short' },
        { email: '', password: 'TestPass123!' },
        { email: 'test@example.com', password: '' }
      ];

      for (const request of invalidRequests) {
        await expect(authService.login(request as LoginRequest))
          .rejects.toThrow(ValidationError);
      }
    });
  });

  describe('JWT Token Management', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
    });

    it('should validate correct JWT tokens', async () => {
      const authToken = await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      const validatedUser = await authService.validateJwtToken(authToken.token);

      expect(validatedUser.id).toBe(testUser.id);
      expect(validatedUser.email).toBe(testUser.email);
      expect(validatedUser.role).toBe(testUser.role);
    });

    it('should reject malformed JWT tokens', async () => {
      const malformedTokens = [
        'invalid.token',
        'not.a.jwt.token',
        'header.payload', // Missing signature
        '', // Empty token
        'a.b.c.d' // Too many parts
      ];

      for (const token of malformedTokens) {
        await expect(authService.validateJwtToken(token))
          .rejects.toThrow(AuthenticationError);
      }
    });

    it('should reject tokens for inactive users', async () => {
      const authToken = await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      // Deactivate user
      testUser.isActive = false;
      userRepository.addUser(testUser);

      await expect(authService.validateJwtToken(authToken.token))
        .rejects.toThrow(AuthenticationError);
    });

    it('should reject tokens for non-existent users', async () => {
      const authToken = await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      // Remove user from repository
      userRepository.clear();

      await expect(authService.validateJwtToken(authToken.token))
        .rejects.toThrow(AuthenticationError);
    });
  });

  describe('API Key Management', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
    });

    it('should create API key with valid request', async () => {
      const apiKeyRequest: ApiKeyRequest = {
        name: 'Test API Key',
        permissions: ['read', 'write']
      };

      const apiKey = await authService.createApiKey(testUser.id, apiKeyRequest);

      expect(apiKey).toBeDefined();
      expect(apiKey.id).toBeDefined();
      expect(apiKey.name).toBe(apiKeyRequest.name);
      expect(apiKey.permissions).toEqual(apiKeyRequest.permissions);
      expect(apiKey.userId).toBe(testUser.id);
      expect(apiKey.isActive).toBe(true);
      expect(apiKey.key).toBeDefined();
      expect(apiKey.hashedKey).toBeDefined();
      expect(apiKey.key).not.toBe(apiKey.hashedKey);
      expect(apiKey.createdAt).toBeInstanceOf(Date);
    });

    it('should reject API key creation with invalid request', async () => {
      const invalidRequests = [
        { name: '', permissions: ['read'] },
        { name: 'Test Key', permissions: [] },
        { name: 'Test Key', permissions: [''] }
      ];

      for (const request of invalidRequests) {
        await expect(authService.createApiKey(testUser.id, request as ApiKeyRequest))
          .rejects.toThrow(ValidationError);
      }
    });

    it('should reject API key creation for non-existent user', async () => {
      await expect(authService.createApiKey('non-existent-id', {
        name: 'Test Key',
        permissions: ['read']
      })).rejects.toThrow(AuthenticationError);
    });

    it('should reject API key creation for inactive user', async () => {
      testUser.isActive = false;
      userRepository.addUser(testUser);

      await expect(authService.createApiKey(testUser.id, {
        name: 'Test Key',
        permissions: ['read']
      })).rejects.toThrow(AuthenticationError);
    });

    it('should validate API key correctly', async () => {
      const apiKey = await authService.createApiKey(testUser.id, {
        name: 'Test Key',
        permissions: ['read', 'write']
      });

      const validatedKey = await authService.validateApiKey(apiKey.key);

      expect(validatedKey.id).toBe(apiKey.id);
      expect(validatedKey.name).toBe(apiKey.name);
      expect(validatedKey.permissions).toEqual(apiKey.permissions);
      expect(validatedKey.userId).toBe(testUser.id);
    });

    it('should reject invalid API keys', async () => {
      await expect(authService.validateApiKey('invalid-key'))
        .rejects.toThrow(AuthenticationError);
    });

    it('should revoke API keys', async () => {
      const apiKey = await authService.createApiKey(testUser.id, {
        name: 'Test Key',
        permissions: ['read']
      });

      // Key should work initially
      await expect(authService.validateApiKey(apiKey.key)).resolves.toBeDefined();

      // Revoke the key
      await authService.revokeApiKey(apiKey.id);

      // Key should no longer work
      await expect(authService.validateApiKey(apiKey.key))
        .rejects.toThrow(AuthenticationError);
    });
  });

  describe('Permission Management', () => {
    let adminUser: User;
    let regularUser: User;

    beforeEach(async () => {
      adminUser = await authService.register({
        email: 'admin@example.com',
        password: 'AdminPass123!',
        name: 'Admin User'
      });
      adminUser.role = 'admin';
      userRepository.addUser(adminUser);

      regularUser = await authService.register({
        email: 'user@example.com',
        password: 'UserPass123!',
        name: 'Regular User'
      });
    });

    it('should grant all permissions to admin users', async () => {
      const permissions = ['read', 'write', 'delete', 'admin'];

      for (const permission of permissions) {
        const hasPermission = await authService.checkPermission(adminUser.id, permission);
        expect(hasPermission).toBe(true);
      }
    });

    it('should deny permissions to regular users without API keys', async () => {
      const permissions = ['read', 'write', 'delete'];

      for (const permission of permissions) {
        const hasPermission = await authService.checkPermission(regularUser.id, permission);
        expect(hasPermission).toBe(false);
      }
    });

    it('should grant permissions based on API key permissions', async () => {
      await authService.createApiKey(regularUser.id, {
        name: 'Read Only Key',
        permissions: ['read']
      });

      expect(await authService.checkPermission(regularUser.id, 'read')).toBe(true);
      expect(await authService.checkPermission(regularUser.id, 'write')).toBe(false);
    });

    it('should combine permissions from multiple API keys', async () => {
      await authService.createApiKey(regularUser.id, {
        name: 'Read Key',
        permissions: ['read']
      });

      await authService.createApiKey(regularUser.id, {
        name: 'Write Key',
        permissions: ['write']
      });

      expect(await authService.checkPermission(regularUser.id, 'read')).toBe(true);
      expect(await authService.checkPermission(regularUser.id, 'write')).toBe(true);
      expect(await authService.checkPermission(regularUser.id, 'delete')).toBe(false);
    });

    it('should deny permissions for inactive users', async () => {
      await authService.createApiKey(regularUser.id, {
        name: 'Test Key',
        permissions: ['read', 'write']
      });

      // Deactivate user
      regularUser.isActive = false;
      userRepository.addUser(regularUser);

      expect(await authService.checkPermission(regularUser.id, 'read')).toBe(false);
      expect(await authService.checkPermission(regularUser.id, 'write')).toBe(false);
    });

    it('should deny permissions for non-existent users', async () => {
      expect(await authService.checkPermission('non-existent-id', 'read')).toBe(false);
    });
  });

  describe('Password Management', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'OriginalPass123!',
        name: 'Test User'
      });
    });

    it('should change password with valid current password', async () => {
      await expect(authService.changePassword(
        testUser.id,
        'OriginalPass123!',
        'NewSecurePass123!'
      )).resolves.toBeUndefined();

      // Verify old password no longer works
      await expect(authService.login({
        email: 'test@example.com',
        password: 'OriginalPass123!'
      })).rejects.toThrow(AuthenticationError);

      // Verify new password works
      await expect(authService.login({
        email: 'test@example.com',
        password: 'NewSecurePass123!'
      })).resolves.toBeDefined();
    });

    it('should reject password change with incorrect current password', async () => {
      await expect(authService.changePassword(
        testUser.id,
        'WrongCurrentPass123!',
        'NewSecurePass123!'
      )).rejects.toThrow(AuthenticationError);
    });

    it('should reject password change with weak new password', async () => {
      await expect(authService.changePassword(
        testUser.id,
        'OriginalPass123!',
        'weak'
      )).rejects.toThrow(ValidationError);
    });

    it('should reject password change for non-existent user', async () => {
      await expect(authService.changePassword(
        'non-existent-id',
        'OriginalPass123!',
        'NewSecurePass123!'
      )).rejects.toThrow(AuthenticationError);
    });

    it('should reject password change for inactive user', async () => {
      testUser.isActive = false;
      userRepository.addUser(testUser);

      await expect(authService.changePassword(
        testUser.id,
        'OriginalPass123!',
        'NewSecurePass123!'
      )).rejects.toThrow(AuthenticationError);
    });
  });

  describe('Error Handling', () => {
    it('should throw appropriate error types', async () => {
      // ValidationError for invalid input
      await expect(authService.register({
        email: 'invalid-email',
        password: 'SecurePass123!',
        name: 'Test User'
      })).rejects.toBeInstanceOf(ValidationError);

      // AuthenticationError for invalid credentials
      await expect(authService.login({
        email: 'nonexistent@example.com',
        password: 'TestPass123!'
      })).rejects.toBeInstanceOf(AuthenticationError);

      // RateLimitError when rate limited
      rateLimiter.setAllowAttempts(false);
      await expect(authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      })).rejects.toBeInstanceOf(RateLimitError);
    });

    it('should provide meaningful error messages', async () => {
      await expect(authService.register({
        email: 'invalid-email',
        password: 'SecurePass123!',
        name: 'Test User'
      })).rejects.toThrow('Invalid registration data format');

      await expect(authService.login({
        email: 'nonexistent@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow('Invalid credentials');

      await expect(authService.validateJwtToken('invalid-token'))
        .rejects.toThrow('Invalid token');
    });
  });

  describe('Edge Cases', () => {
    it('should handle empty string inputs gracefully', async () => {
      await expect(authService.register({
        email: '',
        password: '',
        name: ''
      })).rejects.toThrow(ValidationError);

      await expect(authService.login({
        email: '',
        password: ''
      })).rejects.toThrow(ValidationError);
    });

    it('should handle extremely long inputs', async () => {
      const longString = 'a'.repeat(10000);

      await expect(authService.register({
        email: `${longString}@example.com`,
        password: 'SecurePass123!',
        name: longString
      })).rejects.toThrow(ValidationError);
    });

    it('should handle unicode characters in inputs', async () => {
      const unicodeName = '测试用户';
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: unicodeName
      });

      expect(user.name).toBe(unicodeName);
    });

    it('should handle concurrent API key creation', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      // Create multiple API keys concurrently
      const promises = Array.from({ length: 5 }, (_, i) =>
        authService.createApiKey(user.id, {
          name: `Key ${i}`,
          permissions: ['read']
        })
      );

      const apiKeys = await Promise.all(promises);

      // All keys should be unique
      const keySet = new Set(apiKeys.map(key => key.key));
      expect(keySet.size).toBe(5);
    });
  });
});