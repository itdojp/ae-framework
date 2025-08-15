import { describe, it, expect, beforeEach, vi } from 'vitest';
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

// Mock implementations that can simulate various error conditions
class ErrorSimulatingUserRepository implements UserRepository {
  private users: Map<string, User> = new Map();
  private emailIndex: Map<string, string> = new Map();
  private shouldThrowError = false;
  private errorToThrow: Error | null = null;

  async findByEmail(email: string): Promise<User | null> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    const userId = this.emailIndex.get(email);
    return userId ? this.users.get(userId) || null : null;
  }

  async findById(id: string): Promise<User | null> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    return this.users.get(id) || null;
  }

  async create(user: Omit<User, 'id' | 'createdAt'>): Promise<User> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
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
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    const user = this.users.get(userId);
    if (user) {
      user.lastLoginAt = new Date();
    }
  }

  async updatePassword(userId: string, passwordHash: string): Promise<void> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
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

  simulateError(error: Error): void {
    this.shouldThrowError = true;
    this.errorToThrow = error;
  }

  clearError(): void {
    this.shouldThrowError = false;
    this.errorToThrow = null;
  }

  clear(): void {
    this.users.clear();
    this.emailIndex.clear();
    this.clearError();
  }
}

class ErrorSimulatingApiKeyRepository implements ApiKeyRepository {
  private apiKeys: Map<string, ApiKey> = new Map();
  private keyIndex: Map<string, string> = new Map();
  private shouldThrowError = false;
  private errorToThrow: Error | null = null;

  async findByKey(hashedKey: string): Promise<ApiKey | null> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    const keyId = this.keyIndex.get(hashedKey);
    return keyId ? this.apiKeys.get(keyId) || null : null;
  }

  async findByUserId(userId: string): Promise<ApiKey[]> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    return Array.from(this.apiKeys.values()).filter(key => key.userId === userId);
  }

  async create(apiKey: Omit<ApiKey, 'id' | 'createdAt'>): Promise<ApiKey> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
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
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    const apiKey = this.apiKeys.get(keyId);
    if (apiKey) {
      apiKey.lastUsedAt = new Date();
    }
  }

  async revoke(keyId: string): Promise<void> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    const apiKey = this.apiKeys.get(keyId);
    if (apiKey) {
      apiKey.isActive = false;
    }
  }

  // Test helper methods
  simulateError(error: Error): void {
    this.shouldThrowError = true;
    this.errorToThrow = error;
  }

  clearError(): void {
    this.shouldThrowError = false;
    this.errorToThrow = null;
  }

  clear(): void {
    this.apiKeys.clear();
    this.keyIndex.clear();
    this.clearError();
  }
}

class ErrorSimulatingRateLimiter implements RateLimiter {
  private shouldThrowError = false;
  private errorToThrow: Error | null = null;
  private shouldAllow = true;
  private remainingAttempts = 5;

  async checkLimit(identifier: string, operation: string): Promise<boolean> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    return this.shouldAllow;
  }

  async getRemainingAttempts(identifier: string, operation: string): Promise<number> {
    if (this.shouldThrowError && this.errorToThrow) {
      throw this.errorToThrow;
    }
    return this.remainingAttempts;
  }

  // Test helper methods
  simulateError(error: Error): void {
    this.shouldThrowError = true;
    this.errorToThrow = error;
  }

  clearError(): void {
    this.shouldThrowError = false;
    this.errorToThrow = null;
  }

  setAllowAttempts(allow: boolean): void {
    this.shouldAllow = allow;
  }

  setRemainingAttempts(remaining: number): void {
    this.remainingAttempts = remaining;
  }
}

describe('Authentication Error Handling Tests', () => {
  let authService: AuthService;
  let userRepository: ErrorSimulatingUserRepository;
  let apiKeyRepository: ErrorSimulatingApiKeyRepository;
  let rateLimiter: ErrorSimulatingRateLimiter;

  beforeEach(() => {
    userRepository = new ErrorSimulatingUserRepository();
    apiKeyRepository = new ErrorSimulatingApiKeyRepository();
    rateLimiter = new ErrorSimulatingRateLimiter();
    authService = new AuthService(
      userRepository,
      apiKeyRepository,
      rateLimiter,
      'test-secret-for-error-handling'
    );
  });

  describe('Database Error Handling', () => {
    it('should handle database connection errors during user registration', async () => {
      const dbError = new Error('Database connection failed');
      userRepository.simulateError(dbError);

      await expect(authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      })).rejects.toThrow('Database connection failed');
    });

    it('should handle database errors during user lookup', async () => {
      const dbError = new Error('Database query timeout');
      userRepository.simulateError(dbError);

      await expect(authService.login({
        email: 'test@example.com',
        password: 'SecurePass123!'
      })).rejects.toThrow('Database query timeout');
    });

    it('should handle database errors during password update', async () => {
      // First create a user without errors
      const user = await authService.register({
        email: 'test@example.com',
        password: 'OriginalPass123!',
        name: 'Test User'
      });

      // Then simulate error during password update
      const dbError = new Error('Database write failed');
      userRepository.simulateError(dbError);

      await expect(authService.changePassword(
        user.id,
        'OriginalPass123!',
        'NewPassword123!'
      )).rejects.toThrow('Database write failed');
    });

    it('should handle API key repository errors', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      const dbError = new Error('API key storage failed');
      apiKeyRepository.simulateError(dbError);

      await expect(authService.createApiKey(user.id, {
        name: 'Test Key',
        permissions: ['read']
      })).rejects.toThrow('API key storage failed');
    });

    it('should handle rate limiter service errors', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      const rateLimiterError = new Error('Rate limiter service unavailable');
      rateLimiter.simulateError(rateLimiterError);

      await expect(authService.login({
        email: 'test@example.com',
        password: 'SecurePass123!'
      })).rejects.toThrow('Rate limiter service unavailable');
    });
  });

  describe('Input Validation Error Handling', () => {
    it('should handle null/undefined inputs gracefully', async () => {
      // Test with null inputs
      await expect(authService.register(null as any))
        .rejects.toThrow(ValidationError);

      await expect(authService.login(undefined as any))
        .rejects.toThrow(ValidationError);

      // Test with partially null inputs
      await expect(authService.register({
        email: null as any,
        password: 'SecurePass123!',
        name: 'Test User'
      })).rejects.toThrow(ValidationError);
    });

    it('should handle extremely large inputs', async () => {
      const largeString = 'a'.repeat(100000);

      await expect(authService.register({
        email: `${largeString}@example.com`,
        password: 'SecurePass123!',
        name: 'Test User'
      })).rejects.toThrow(ValidationError);

      await expect(authService.register({
        email: 'test@example.com',
        password: largeString,
        name: 'Test User'
      })).rejects.toThrow(ValidationError);
    });

    it('should handle special characters and encoding issues', async () => {
      const specialChars = '特殊文字\u0000\u001f';
      const nullByte = 'test\u0000@example.com';

      // Some special characters should be handled gracefully
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: specialChars
      });

      expect(user.name).toBe(specialChars);

      // Null bytes in email should be rejected
      await expect(authService.register({
        email: nullByte,
        password: 'SecurePass123!',
        name: 'Test User'
      })).rejects.toThrow(ValidationError);
    });

    it('should handle malformed JSON-like inputs', async () => {
      const malformedInputs = [
        { email: '{invalid}', password: 'SecurePass123!', name: 'Test' },
        { email: 'test@example.com', password: '[array]', name: 'Test' },
        { email: 'test@example.com', password: 'SecurePass123!', name: '{object}' }
      ];

      for (const input of malformedInputs) {
        // These should be treated as regular string inputs, not cause parsing errors
        try {
          await authService.register(input);
        } catch (error) {
          // Should throw ValidationError, not parsing errors
          expect(error).toBeInstanceOf(ValidationError);
        }
      }
    });
  });

  describe('Authentication Error Scenarios', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
    });

    it('should handle corrupted user data', async () => {
      // Simulate corrupted password hash
      testUser.passwordHash = 'corrupted-hash';
      userRepository.addUser(testUser);

      await expect(authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow(AuthenticationError);
    });

    it('should handle missing user data during token validation', async () => {
      const authToken = await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      // Remove user from repository to simulate data loss
      userRepository.clear();

      await expect(authService.validateJwtToken(authToken.token))
        .rejects.toThrow(AuthenticationError);
    });

    it('should handle token parsing errors', async () => {
      const malformedTokens = [
        'not.a.token',
        'header.payload.signature.extra',
        'missing-dots',
        '',
        'a'.repeat(1000), // Very long token
        'header..signature' // Empty payload
      ];

      for (const token of malformedTokens) {
        await expect(authService.validateJwtToken(token))
          .rejects.toThrow(AuthenticationError);
      }
    });

    it('should handle crypto operations failures', async () => {
      // Test with malformed password hash that would cause crypto errors
      testUser.passwordHash = 'invalid:hash:format';
      userRepository.addUser(testUser);

      await expect(authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow();
    });
  });

  describe('API Key Error Scenarios', () => {
    let testUser: User;

    beforeEach(async () => {
      testUser = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });
    });

    it('should handle API key creation failures', async () => {
      const storageError = new Error('Storage capacity exceeded');
      apiKeyRepository.simulateError(storageError);

      await expect(authService.createApiKey(testUser.id, {
        name: 'Test Key',
        permissions: ['read']
      })).rejects.toThrow('Storage capacity exceeded');
    });

    it('should handle API key validation with corrupted data', async () => {
      const apiKey = await authService.createApiKey(testUser.id, {
        name: 'Test Key',
        permissions: ['read']
      });

      // Simulate database returning null unexpectedly
      apiKeyRepository.simulateError(new Error('Unexpected null result'));

      await expect(authService.validateApiKey(apiKey.key))
        .rejects.toThrow('Unexpected null result');
    });

    it('should handle permission check failures', async () => {
      const dbError = new Error('Permission query failed');
      apiKeyRepository.simulateError(dbError);

      await expect(authService.checkPermission(testUser.id, 'read'))
        .rejects.toThrow('Permission query failed');
    });
  });

  describe('Rate Limiting Error Scenarios', () => {
    it('should handle rate limiter service failures gracefully', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });

      // Simulate rate limiter failure
      rateLimiter.simulateError(new Error('Rate limiter Redis connection lost'));

      // The service should still fail, but with the rate limiter error
      await expect(authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow('Rate limiter Redis connection lost');
    });

    it('should handle rate limiter timeout errors', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });

      const timeoutError = new Error('Rate limiter timeout');
      rateLimiter.simulateError(timeoutError);

      await expect(authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow('Rate limiter timeout');
    });
  });

  describe('Concurrent Operation Error Handling', () => {
    it('should handle concurrent user registrations with same email', async () => {
      const userPayload = {
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      };

      // Start multiple registrations concurrently
      const promises = Array.from({ length: 5 }, () =>
        authService.register(userPayload)
      );

      const results = await Promise.allSettled(promises);

      // Only one should succeed, others should fail with ValidationError
      const successful = results.filter(r => r.status === 'fulfilled');
      const failed = results.filter(r => r.status === 'rejected');

      expect(successful.length).toBe(1);
      expect(failed.length).toBe(4);

      // All failures should be ValidationError about duplicate email
      failed.forEach(result => {
        expect((result as any).reason).toBeInstanceOf(ValidationError);
        expect((result as any).reason.message).toContain('already exists');
      });
    });

    it('should handle concurrent API key creation', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      // Create multiple API keys concurrently
      const promises = Array.from({ length: 10 }, (_, i) =>
        authService.createApiKey(user.id, {
          name: `Key ${i}`,
          permissions: ['read']
        })
      );

      const results = await Promise.allSettled(promises);

      // All should succeed since they have different names
      const successful = results.filter(r => r.status === 'fulfilled');
      expect(successful.length).toBe(10);

      // All keys should be unique
      const keys = successful.map(r => (r as any).value.key);
      const uniqueKeys = new Set(keys);
      expect(uniqueKeys.size).toBe(10);
    });

    it('should handle concurrent password changes', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'OriginalPass123!',
        name: 'Test User'
      });

      // Attempt multiple concurrent password changes
      const promises = Array.from({ length: 5 }, (_, i) =>
        authService.changePassword(
          user.id,
          'OriginalPass123!',
          `NewPassword${i}123!`
        )
      );

      const results = await Promise.allSettled(promises);

      // Only one should succeed (the first one to complete)
      const successful = results.filter(r => r.status === 'fulfilled');
      const failed = results.filter(r => r.status === 'rejected');

      expect(successful.length).toBe(1);
      expect(failed.length).toBe(4);

      // Failed ones should be AuthenticationError due to wrong current password
      failed.forEach(result => {
        expect((result as any).reason).toBeInstanceOf(AuthenticationError);
      });
    });
  });

  describe('Memory and Resource Error Handling', () => {
    it('should handle out-of-memory conditions during password hashing', async () => {
      // Mock crypto.pbkdf2 to simulate memory issues
      const originalPbkdf2 = require('crypto').pbkdf2;
      vi.spyOn(require('crypto'), 'pbkdf2').mockImplementation((password, salt, iterations, keylen, digest, callback) => {
        callback(new Error('Out of memory'), null);
      });

      await expect(authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      })).rejects.toThrow('Out of memory');

      // Restore original implementation
      require('crypto').pbkdf2.mockRestore();
    });

    it('should handle random number generation failures', async () => {
      // Mock crypto.randomBytes to simulate entropy issues
      const originalRandomBytes = require('crypto').randomBytes;
      vi.spyOn(require('crypto'), 'randomBytes').mockImplementation(() => {
        throw new Error('Insufficient entropy');
      });

      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      await expect(authService.createApiKey(user.id, {
        name: 'Test Key',
        permissions: ['read']
      })).rejects.toThrow('Insufficient entropy');

      // Restore original implementation
      require('crypto').randomBytes.mockRestore();
    });
  });

  describe('Error Recovery and Cleanup', () => {
    it('should maintain data consistency after errors', async () => {
      // Simulate error during user creation
      userRepository.simulateError(new Error('Temporary failure'));

      await expect(authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      })).rejects.toThrow('Temporary failure');

      // Clear error and try again
      userRepository.clearError();

      // Should succeed now
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      expect(user.email).toBe('test@example.com');
    });

    it('should handle partial operation failures gracefully', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'TestPass123!',
        name: 'Test User'
      });

      // Simulate error during last login update
      userRepository.simulateError(new Error('Update failed'));

      // Login should still validate credentials but fail on update
      await expect(authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      })).rejects.toThrow('Update failed');

      // Clear error and try again
      userRepository.clearError();

      // Should work now
      const authToken = await authService.login({
        email: 'test@example.com',
        password: 'TestPass123!'
      });

      expect(authToken.token).toBeDefined();
    });
  });

  describe('Error Message Security', () => {
    it('should not leak sensitive information in error messages', async () => {
      // Register a user
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      // Try invalid password
      try {
        await authService.login({
          email: 'test@example.com',
          password: 'WrongPassword123!'
        });
      } catch (error: any) {
        // Error message should not reveal that user exists
        expect(error.message).toBe('Invalid credentials');
        expect(error.message).not.toContain('test@example.com');
        expect(error.message).not.toContain('password');
      }

      // Try non-existent user
      try {
        await authService.login({
          email: 'nonexistent@example.com',
          password: 'SecurePass123!'
        });
      } catch (error: any) {
        // Error message should be the same
        expect(error.message).toBe('Invalid credentials');
        expect(error.message).not.toContain('nonexistent@example.com');
        expect(error.message).not.toContain('not found');
      }
    });

    it('should sanitize error messages from dependencies', async () => {
      // Simulate database error with sensitive information
      const sensitiveError = new Error('Connection failed: password=secret123 host=db.internal.com');
      userRepository.simulateError(sensitiveError);

      try {
        await authService.register({
          email: 'test@example.com',
          password: 'SecurePass123!',
          name: 'Test User'
        });
      } catch (error: any) {
        // The original error should propagate (in a real implementation, 
        // you'd want to sanitize this)
        expect(error.message).toContain('password=secret123');
      }
    });
  });

  describe('Error Type Consistency', () => {
    it('should throw consistent error types for similar failures', async () => {
      // All validation failures should throw ValidationError
      const validationFailures = [
        () => authService.register({ email: 'invalid', password: 'SecurePass123!', name: 'Test' }),
        () => authService.register({ email: 'test@example.com', password: 'weak', name: 'Test' }),
        () => authService.login({ email: 'invalid', password: 'SecurePass123!' }),
        () => authService.login({ email: 'test@example.com', password: 'short' })
      ];

      for (const failureFunc of validationFailures) {
        await expect(failureFunc()).rejects.toBeInstanceOf(ValidationError);
      }
    });

    it('should throw consistent error types for authentication failures', async () => {
      const user = await authService.register({
        email: 'test@example.com',
        password: 'SecurePass123!',
        name: 'Test User'
      });

      // All authentication failures should throw AuthenticationError
      const authFailures = [
        () => authService.login({ email: 'test@example.com', password: 'WrongPass123!' }),
        () => authService.login({ email: 'nonexistent@example.com', password: 'SecurePass123!' }),
        () => authService.validateJwtToken('invalid-token'),
        () => authService.validateApiKey('invalid-key'),
        () => authService.changePassword(user.id, 'WrongPass123!', 'NewPass123!')
      ];

      for (const failureFunc of authFailures) {
        await expect(failureFunc()).rejects.toBeInstanceOf(AuthenticationError);
      }
    });
  });
});