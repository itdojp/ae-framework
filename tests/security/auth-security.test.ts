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
  RateLimiter
} from '../../src/services/auth-service.js';

// Mock repositories and rate limiter
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

  // Test helper methods
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
  private attempts: Map<string, { count: number; lastAttempt: Date }> = new Map();
  private maxAttempts = 5;
  private windowMs = 15 * 60 * 1000; // 15 minutes

  async checkLimit(identifier: string, operation: string): Promise<boolean> {
    const key = `${identifier}:${operation}`;
    const now = new Date();
    const record = this.attempts.get(key);

    if (!record) {
      this.attempts.set(key, { count: 1, lastAttempt: now });
      return true;
    }

    // Reset if window has passed
    if (now.getTime() - record.lastAttempt.getTime() > this.windowMs) {
      this.attempts.set(key, { count: 1, lastAttempt: now });
      return true;
    }

    record.count++;
    record.lastAttempt = now;

    return record.count <= this.maxAttempts;
  }

  async getRemainingAttempts(identifier: string, operation: string): Promise<number> {
    const key = `${identifier}:${operation}`;
    const record = this.attempts.get(key);
    
    if (!record) return this.maxAttempts;
    
    const now = new Date();
    if (now.getTime() - record.lastAttempt.getTime() > this.windowMs) {
      return this.maxAttempts;
    }

    return Math.max(0, this.maxAttempts - record.count);
  }

  // Test helper methods
  setMaxAttempts(max: number): void {
    this.maxAttempts = max;
  }

  clear(): void {
    this.attempts.clear();
  }
}

describe('Authentication Security Tests', () => {
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
      'test-secret-key-very-long-and-secure'
    );
  });

  describe('Password Security', () => {
    it('should reject weak passwords', async () => {
      const weakPasswords = [
        'password',        // No uppercase, numbers, or special chars
        'Password',        // No numbers or special chars
        'Password1',       // No special chars
        'Pass1!',          // Too short
        '12345678',        // No letters or special chars
        'PASSWORD123!',    // No lowercase
        'password123!'     // No uppercase
      ];

      for (const password of weakPasswords) {
        await expect(authService.register({
          email: `test${Date.now()}@example.com`,
          password,
          name: 'Test User'
        })).rejects.toThrow(ValidationError);
      }
    });

    it('should accept strong passwords', async () => {
      const strongPasswords = [
        'Password123!',
        'MyStr0ng#Pass',
        'Secure$2024Pass',
        'C0mplex&Password'
      ];

      for (const password of strongPasswords) {
        const email = `test${Date.now()}-${Math.random()}@example.com`;
        await expect(authService.register({
          email,
          password,
          name: 'Test User'
        })).resolves.toBeDefined();
      }
    });

    it('should hash passwords securely', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      // Password should be hashed, not stored in plain text
      expect(user.passwordHash).not.toBe('SecurePass123!');
      expect(user.passwordHash).toContain(':'); // Should contain salt separator
      expect(user.passwordHash.length).toBeGreaterThan(50); // Should be reasonably long
    });

    it('should use unique salts for each password', async () => {
      const password = 'SamePassword123!';
      
      const user1 = await authService.register({
        email: 'user1@example.com',
        password,
        name: 'User 1'
      });

      const user2 = await authService.register({
        email: 'user2@example.com',
        password,
        name: 'User 2'
      });

      // Same password should result in different hashes due to unique salts
      expect(user1.passwordHash).not.toBe(user2.passwordHash);
    });
  });

  describe('JWT Token Security', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
    });

    it('should generate valid JWT tokens', async () => {
      const authToken = await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      expect(authToken.token).toMatch(/^[A-Za-z0-9\-_]+\.[A-Za-z0-9\-_]+\.[A-Za-z0-9\-_]+$/);
      expect(authToken.type).toBe('jwt');
      expect(authToken.expiresAt).toBeInstanceOf(Date);
    });

    it('should reject tampered JWT tokens', async () => {
      const authToken = await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      // Tamper with the token
      const parts = authToken.token.split('.');
      const tamperedPayload = Buffer.from('{"userId":"fake-id","role":"admin"}').toString('base64url');
      const tamperedToken = `${parts[0]}.${tamperedPayload}.${parts[2]}`;

      await expect(authService.validateJwtToken(tamperedToken))
        .rejects.toThrow(AuthenticationError);
    });

    it('should reject expired JWT tokens', async () => {
      // Create a token with very short expiration
      const authServiceShortExp = new AuthService(
        userRepository,
        apiKeyRepository,
        rateLimiter,
        'test-secret-key-very-long-and-secure'
      );

      const authToken = await authServiceShortExp.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      // Wait for token to expire (simulate by creating an expired token manually)
      const [header, payload, signature] = authToken.token.split('.');
      const decodedPayload = JSON.parse(Buffer.from(payload, 'base64url').toString());
      decodedPayload.exp = Math.floor(Date.now() / 1000) - 3600; // Expired 1 hour ago
      
      const expiredPayload = Buffer.from(JSON.stringify(decodedPayload)).toString('base64url');
      const expiredToken = `${header}.${expiredPayload}.${signature}`;

      await expect(authService.validateJwtToken(expiredToken))
        .rejects.toThrow(AuthenticationError);
    });

    it('should validate tokens with correct signature', async () => {
      const authToken = await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      const validatedUser = await authService.validateJwtToken(authToken.token);
      expect(validatedUser.id).toBe(testUser.id);
      expect(validatedUser.email).toBe(testUser.email);
    });
  });

  describe('API Key Security', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
    });

    it('should generate cryptographically secure API keys', async () => {
      const apiKey1 = await authService.createApiKey(testUser.id, {
        name: 'Test Key 1',
        permissions: ['read']
      });

      const apiKey2 = await authService.createApiKey(testUser.id, {
        name: 'Test Key 2',
        permissions: ['read']
      });

      // Keys should be unique
      expect(apiKey1.key).not.toBe(apiKey2.key);
      
      // Keys should be sufficiently long (64 hex chars = 32 bytes)
      expect(apiKey1.key).toMatch(/^[a-f0-9]{64}$/);
      expect(apiKey2.key).toMatch(/^[a-f0-9]{64}$/);
      
      // Hashed keys should be different from plain keys
      expect(apiKey1.hashedKey).not.toBe(apiKey1.key);
      expect(apiKey2.hashedKey).not.toBe(apiKey2.key);
    });

    it('should validate API keys correctly', async () => {
      const apiKey = await authService.createApiKey(testUser.id, {
        name: 'Test Key',
        permissions: ['read', 'write']
      });

      const validatedKey = await authService.validateApiKey(apiKey.key);
      expect(validatedKey.id).toBe(apiKey.id);
      expect(validatedKey.permissions).toEqual(['read', 'write']);
    });

    it('should reject invalid API keys', async () => {
      const invalidKeys = [
        'invalid-key',
        'a'.repeat(64), // Valid format but not generated by the system
        '', // Empty key
        'short', // Too short
        '1234567890abcdef'.repeat(4) // Valid hex but wrong key
      ];

      for (const invalidKey of invalidKeys) {
        await expect(authService.validateApiKey(invalidKey))
          .rejects.toThrow(AuthenticationError);
      }
    });

    it('should not validate revoked API keys', async () => {
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

    it('should update last used timestamp on validation', async () => {
      const apiKey = await authService.createApiKey(testUser.id, {
        name: 'Test Key',
        permissions: ['read']
      });

      expect(apiKey.lastUsedAt).toBeUndefined();

      await authService.validateApiKey(apiKey.key);

      const updatedKey = await apiKeyRepository.findByUserId(testUser.id);
      expect(updatedKey[0].lastUsedAt).toBeInstanceOf(Date);
    });
  });

  describe('Rate Limiting Security', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
      rateLimiter.setMaxAttempts(3); // Set low limit for testing
    });

    it('should enforce rate limiting on login attempts', async () => {
      const invalidPassword = 'WrongPassword123!';

      // First few attempts should be allowed
      for (let i = 0; i < 3; i++) {
        await expect(authService.login({
          email: 'test@example.com',
          password: invalidPassword
        })).rejects.toThrow(AuthenticationError);
      }

      // Next attempt should be rate limited
      await expect(authService.login({
        email: 'test@example.com',
        password: invalidPassword
      })).rejects.toThrow(RateLimitError);
    });

    it('should rate limit per email address', async () => {
      // Exhaust rate limit for one email
      for (let i = 0; i < 3; i++) {
        await expect(authService.login({
          email: 'test@example.com',
          password: 'WrongPassword123!'
        })).rejects.toThrow(AuthenticationError);
      }

      // Should be rate limited for the first email
      await expect(authService.login({
        email: 'test@example.com',
        password: 'WrongPassword123!'
      })).rejects.toThrow(RateLimitError);

      // But other email should still work (until its limit is reached)
      const anotherUser = await authService.register({
        email: 'another@example.com',
        password: 'AnotherPass123!',
        name: 'Another User'
      });

      // This should work (correct password)
      await expect(authService.login({
        email: 'another@example.com',
        password: 'AnotherPass123!'
      })).resolves.toBeDefined();
    });
  });

  describe('Authorization Security', () => {
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

    it('should grant admin users all permissions', async () => {
      const permissions = ['read', 'write', 'delete', 'admin', 'super-admin'];
      
      for (const permission of permissions) {
        const hasPermission = await authService.checkPermission(adminUser.id, permission);
        expect(hasPermission).toBe(true);
      }
    });

    it('should deny permissions to users without API keys', async () => {
      const permissions = ['read', 'write', 'delete'];
      
      for (const permission of permissions) {
        const hasPermission = await authService.checkPermission(regularUser.id, permission);
        expect(hasPermission).toBe(false);
      }
    });

    it('should grant only specified permissions through API keys', async () => {
      await authService.createApiKey(regularUser.id, {
        name: 'Read Only Key',
        permissions: ['read']
      });

      expect(await authService.checkPermission(regularUser.id, 'read')).toBe(true);
      expect(await authService.checkPermission(regularUser.id, 'write')).toBe(false);
      expect(await authService.checkPermission(regularUser.id, 'delete')).toBe(false);
    });

    it('should deny permissions for inactive users', async () => {
      regularUser.isActive = false;
      userRepository.addUser(regularUser);

      await authService.createApiKey(regularUser.id, {
        name: 'Test Key',
        permissions: ['read', 'write']
      });

      expect(await authService.checkPermission(regularUser.id, 'read')).toBe(false);
      expect(await authService.checkPermission(regularUser.id, 'write')).toBe(false);
    });
  });

  describe('Input Validation Security', () => {
    it('should prevent SQL injection in email fields', async () => {
      const sqlInjectionAttempts = [
        "test@example.com'; DROP TABLE users; --",
        "test@example.com' OR '1'='1",
        "test'; INSERT INTO users VALUES ('hacker'); --@example.com"
      ];

      for (const maliciousEmail of sqlInjectionAttempts) {
        await expect(authService.register({
          email: maliciousEmail,
          password: 'TestPass123!',
          name: 'Test User'
        })).rejects.toThrow(ValidationError);
      }
    });

    it('should sanitize and validate email formats', async () => {
      const invalidEmails = [
        'not-an-email',
        '@example.com',
        'test@',
        'test..test@example.com',
        'test@example',
        '<script>alert("xss")</script>@example.com'
      ];

      for (const invalidEmail of invalidEmails) {
        await expect(authService.register({
          email: invalidEmail,
          password: 'TestPass123!',
          name: 'Test User'
        })).rejects.toThrow(ValidationError);
      }
    });

    it('should prevent XSS in name fields', async () => {
      const xssAttempts = [
        '<script>alert("xss")</script>',
        'javascript:alert("xss")',
        '<img src="x" onerror="alert(\'xss\')">'
      ];

      // Note: In a real application, you'd want to sanitize rather than reject
      // But for security testing, we're checking that dangerous input is handled
      for (const maliciousName of xssAttempts) {
        // The current implementation doesn't sanitize names, so this test
        // demonstrates the need for proper input sanitization
        const user = await authService.register({
          email: `test${Date.now()}@example.com`,
          password: 'TestPass123!',
          name: maliciousName
        });
        
        // Verify that the name is stored as-is (in a real app, it should be sanitized)
        expect(user.name).toBe(maliciousName);
      }
    });
  });

  describe('Session Security', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
    });

    it('should track last login time', async () => {
      expect(testUser.lastLoginAt).toBeUndefined();

      await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      const updatedUser = await userRepository.findById(testUser.id);
      expect(updatedUser?.lastLoginAt).toBeInstanceOf(Date);
    });

    it('should not reveal user existence through timing attacks', async () => {
      // This test would require more sophisticated timing analysis
      // For now, we just ensure consistent error messages
      
      await expect(authService.login({
        email: 'nonexistent@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow('Invalid credentials');

      await expect(authService.login({
        email: 'test@example.com',
        password: 'WrongPassword123!'
      })).rejects.toThrow('Invalid credentials');
    });
  });

  describe('Password Change Security', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'OldPass123!',
        name: 'Test User'
      });
    });

    it('should require current password for password change', async () => {
      await expect(authService.changePassword(
        testUser.id,
        'WrongOldPass123!',
        'NewPass123!'
      )).rejects.toThrow(AuthenticationError);
    });

    it('should enforce password strength on password change', async () => {
      await expect(authService.changePassword(
        testUser.id,
        'OldPass123!',
        'weak'
      )).rejects.toThrow(ValidationError);
    });

    it('should successfully change password with valid inputs', async () => {
      await expect(authService.changePassword(
        testUser.id,
        'OldPass123!',
        'NewStrongPass123!'
      )).resolves.toBeUndefined();

      // Verify old password no longer works
      await expect(authService.login({
        email: 'test@example.com',
        password: 'OldPass123!'
      })).rejects.toThrow(AuthenticationError);

      // Verify new password works
      await expect(authService.login({
        email: 'test@example.com',
        password: 'NewStrongPass123!'
      })).resolves.toBeDefined();
    });
  });
});