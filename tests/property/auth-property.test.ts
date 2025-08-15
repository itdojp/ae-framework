import { describe, it, expect, beforeEach } from 'vitest';
import fc from 'fast-check';
import * as crypto from 'crypto';
import {
  AuthService,
  User,
  ApiKey,
  UserRepository,
  ApiKeyRepository,
  RateLimiter,
  ValidationError,
  AuthenticationError
} from '../../src/services/auth-service.js';

// Simple in-memory implementations for property testing
class PropertyTestUserRepository implements UserRepository {
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

  clear(): void {
    this.users.clear();
    this.emailIndex.clear();
  }
}

class PropertyTestApiKeyRepository implements ApiKeyRepository {
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

class PropertyTestRateLimiter implements RateLimiter {
  async checkLimit(identifier: string, operation: string): Promise<boolean> {
    return true; // Always allow for property testing
  }

  async getRemainingAttempts(identifier: string, operation: string): Promise<number> {
    return 100; // High limit for property testing
  }
}

// Custom arbitraries for testing
const validEmailArbitrary = fc.tuple(
  fc.stringOf(fc.char().filter(c => /[a-zA-Z0-9._-]/.test(c)), { minLength: 1, maxLength: 64 }),
  fc.constantFrom('gmail.com', 'example.com', 'test.org', 'company.net')
).map(([local, domain]) => `${local}@${domain}`);

const strongPasswordArbitrary = fc.tuple(
  fc.stringOf(fc.char().filter(c => /[a-z]/.test(c)), { minLength: 1, maxLength: 10 }),
  fc.stringOf(fc.char().filter(c => /[A-Z]/.test(c)), { minLength: 1, maxLength: 10 }),
  fc.stringOf(fc.char().filter(c => /[0-9]/.test(c)), { minLength: 1, maxLength: 10 }),
  fc.stringOf(fc.char().filter(c => /[@$!%*?&]/.test(c)), { minLength: 1, maxLength: 10 })
).map(([lower, upper, digit, special]) => {
  const combined = lower + upper + digit + special;
  return combined.split('').sort(() => Math.random() - 0.5).join('');
});

const weakPasswordArbitrary = fc.oneof(
  fc.string({ minLength: 1, maxLength: 7 }), // Too short
  fc.stringOf(fc.char().filter(c => /[a-z]/.test(c)), { minLength: 8, maxLength: 20 }), // Only lowercase
  fc.stringOf(fc.char().filter(c => /[0-9]/.test(c)), { minLength: 8, maxLength: 20 }), // Only numbers
  fc.constant('password123') // Common weak password
);

const nameArbitrary = fc.stringOf(
  fc.char().filter(c => /[a-zA-Z\s\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FAF]/.test(c)),
  { minLength: 1, maxLength: 100 }
).filter(name => name.trim().length >= 2);

const permissionArbitrary = fc.array(
  fc.constantFrom('read', 'write', 'delete', 'admin', 'user', 'api', 'billing'),
  { minLength: 1, maxLength: 5 }
);

describe('Authentication Property-Based Tests', () => {
  let authService: AuthService;
  let userRepository: PropertyTestUserRepository;
  let apiKeyRepository: PropertyTestApiKeyRepository;
  let rateLimiter: PropertyTestRateLimiter;

  beforeEach(() => {
    userRepository = new PropertyTestUserRepository();
    apiKeyRepository = new PropertyTestApiKeyRepository();
    rateLimiter = new PropertyTestRateLimiter();
    authService = new AuthService(
      userRepository,
      apiKeyRepository,
      rateLimiter,
      'property-test-secret-key'
    );
  });

  describe('User Registration Properties', () => {
    it('should always create unique user IDs', () => {
      fc.assert(fc.asyncProperty(
        fc.array(fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary), { minLength: 2, maxLength: 10 }),
        async (userInputs) => {
          userRepository.clear();
          
          const users: User[] = [];
          
          for (const [email, password, name] of userInputs) {
            try {
              const user = await authService.register({ email, password, name });
              users.push(user);
            } catch (error) {
              // Skip validation errors for property testing
              if (!(error instanceof ValidationError)) {
                throw error;
              }
            }
          }

          // All user IDs should be unique
          const userIds = users.map(u => u.id);
          const uniqueIds = new Set(userIds);
          expect(uniqueIds.size).toBe(userIds.length);
        }
      ));
    });

    it('should never store passwords in plain text', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary),
        async ([email, password, name]) => {
          userRepository.clear();
          
          try {
            const user = await authService.register({ email, password, name });
            
            // Password hash should never equal the original password
            expect(user.passwordHash).not.toBe(password);
            
            // Password hash should contain salt separator
            expect(user.passwordHash).toContain(':');
            
            // Password hash should be significantly longer than original
            expect(user.passwordHash.length).toBeGreaterThan(password.length + 20);
          } catch (error) {
            // Skip validation errors
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });

    it('should reject weak passwords consistently', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, weakPasswordArbitrary, nameArbitrary),
        async ([email, password, name]) => {
          userRepository.clear();
          
          await expect(authService.register({ email, password, name }))
            .rejects.toThrow(ValidationError);
        }
      ));
    });

    it('should preserve user data integrity', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary),
        async ([email, password, name]) => {
          userRepository.clear();
          
          try {
            const user = await authService.register({ email, password, name });
            
            // User data should be preserved exactly
            expect(user.email).toBe(email);
            expect(user.name).toBe(name);
            expect(user.role).toBe('user');
            expect(user.isActive).toBe(true);
            expect(user.createdAt).toBeInstanceOf(Date);
            expect(user.id).toBeDefined();
          } catch (error) {
            // Skip validation errors
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });
  });

  describe('Authentication Properties', () => {
    it('should always authenticate users with correct credentials', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary),
        async ([email, password, name]) => {
          userRepository.clear();
          
          try {
            // Register user
            await authService.register({ email, password, name });
            
            // Should always be able to login with correct credentials
            const authToken = await authService.login({ email, password });
            
            expect(authToken.token).toBeDefined();
            expect(authToken.type).toBe('jwt');
            expect(authToken.user.email).toBe(email);
            expect(authToken.expiresAt).toBeInstanceOf(Date);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });

    it('should never authenticate with wrong passwords', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, strongPasswordArbitrary, nameArbitrary),
        async ([email, correctPassword, wrongPassword, name]) => {
          fc.pre(correctPassword !== wrongPassword); // Ensure passwords are different
          
          userRepository.clear();
          
          try {
            // Register user
            await authService.register({ email, password: correctPassword, name });
            
            // Should never authenticate with wrong password
            await expect(authService.login({ email, password: wrongPassword }))
              .rejects.toThrow(AuthenticationError);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });

    it('should generate unique tokens for each login', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary),
        async ([email, password, name]) => {
          userRepository.clear();
          
          try {
            // Register user
            await authService.register({ email, password, name });
            
            // Login multiple times
            const tokens: string[] = [];
            for (let i = 0; i < 5; i++) {
              const authToken = await authService.login({ email, password });
              tokens.push(authToken.token);
              
              // Small delay to ensure different timestamps
              await new Promise(resolve => setTimeout(resolve, 1));
            }
            
            // All tokens should be unique
            const uniqueTokens = new Set(tokens);
            expect(uniqueTokens.size).toBe(tokens.length);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });
  });

  describe('JWT Token Properties', () => {
    it('should always validate self-generated tokens', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary),
        async ([email, password, name]) => {
          userRepository.clear();
          
          try {
            // Register and login
            const user = await authService.register({ email, password, name });
            const authToken = await authService.login({ email, password });
            
            // Should always validate its own tokens
            const validatedUser = await authService.validateJwtToken(authToken.token);
            
            expect(validatedUser.id).toBe(user.id);
            expect(validatedUser.email).toBe(user.email);
            expect(validatedUser.role).toBe(user.role);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });

    it('should never validate tampered tokens', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary, fc.string({ minLength: 1, maxLength: 100 })),
        async ([email, password, name, tamperString]) => {
          userRepository.clear();
          
          try {
            // Register and login
            await authService.register({ email, password, name });
            const authToken = await authService.login({ email, password });
            
            // Tamper with the token
            const tamperedToken = authToken.token + tamperString;
            
            // Should never validate tampered token
            await expect(authService.validateJwtToken(tamperedToken))
              .rejects.toThrow(AuthenticationError);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });
  });

  describe('API Key Properties', () => {
    it('should always generate unique API keys', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary, fc.array(permissionArbitrary, { minLength: 1, maxLength: 5 })),
        async ([email, password, name, keyPermissions]) => {
          userRepository.clear();
          apiKeyRepository.clear();
          
          try {
            // Register user
            const user = await authService.register({ email, password, name });
            
            // Create multiple API keys
            const apiKeys: ApiKey[] = [];
            for (let i = 0; i < keyPermissions.length; i++) {
              const apiKey = await authService.createApiKey(user.id, {
                name: `Key ${i}`,
                permissions: keyPermissions[i]
              });
              apiKeys.push(apiKey);
            }
            
            // All API keys should be unique
            const keys = apiKeys.map(k => k.key);
            const uniqueKeys = new Set(keys);
            expect(uniqueKeys.size).toBe(keys.length);
            
            // All hashed keys should be unique
            const hashedKeys = apiKeys.map(k => k.hashedKey);
            const uniqueHashedKeys = new Set(hashedKeys);
            expect(uniqueHashedKeys.size).toBe(hashedKeys.length);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });

    it('should always validate self-generated API keys', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary, permissionArbitrary),
        async ([email, password, name, permissions]) => {
          userRepository.clear();
          apiKeyRepository.clear();
          
          try {
            // Register user and create API key
            const user = await authService.register({ email, password, name });
            const apiKey = await authService.createApiKey(user.id, {
              name: 'Test Key',
              permissions
            });
            
            // Should always validate its own API keys
            const validatedKey = await authService.validateApiKey(apiKey.key);
            
            expect(validatedKey.id).toBe(apiKey.id);
            expect(validatedKey.userId).toBe(user.id);
            expect(validatedKey.permissions).toEqual(permissions);
            expect(validatedKey.isActive).toBe(true);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });

    it('should preserve permission integrity', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary, permissionArbitrary),
        async ([email, password, name, permissions]) => {
          userRepository.clear();
          apiKeyRepository.clear();
          
          try {
            // Register user and create API key
            const user = await authService.register({ email, password, name });
            const apiKey = await authService.createApiKey(user.id, {
              name: 'Test Key',
              permissions
            });
            
            // Permissions should be preserved exactly
            expect(apiKey.permissions).toEqual(permissions);
            
            // Permission checks should be consistent
            for (const permission of permissions) {
              const hasPermission = await authService.checkPermission(user.id, permission);
              expect(hasPermission).toBe(true);
            }
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });
  });

  describe('Password Change Properties', () => {
    it('should always work with correct current password', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, strongPasswordArbitrary, nameArbitrary),
        async ([email, oldPassword, newPassword, name]) => {
          fc.pre(oldPassword !== newPassword); // Ensure passwords are different
          
          userRepository.clear();
          
          try {
            // Register user
            const user = await authService.register({ email, password: oldPassword, name });
            
            // Change password
            await authService.changePassword(user.id, oldPassword, newPassword);
            
            // Should be able to login with new password
            const authToken = await authService.login({ email, password: newPassword });
            expect(authToken.user.email).toBe(email);
            
            // Should not be able to login with old password
            await expect(authService.login({ email, password: oldPassword }))
              .rejects.toThrow(AuthenticationError);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });

    it('should never work with incorrect current password', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, strongPasswordArbitrary, strongPasswordArbitrary, nameArbitrary),
        async ([email, correctPassword, wrongPassword, newPassword, name]) => {
          fc.pre(correctPassword !== wrongPassword && correctPassword !== newPassword && wrongPassword !== newPassword);
          
          userRepository.clear();
          
          try {
            // Register user
            const user = await authService.register({ email, password: correctPassword, name });
            
            // Should fail to change password with wrong current password
            await expect(authService.changePassword(user.id, wrongPassword, newPassword))
              .rejects.toThrow(AuthenticationError);
            
            // Original password should still work
            const authToken = await authService.login({ email, password: correctPassword });
            expect(authToken.user.email).toBe(email);
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });
  });

  describe('System Invariants', () => {
    it('should maintain user uniqueness invariant', () => {
      fc.assert(fc.asyncProperty(
        fc.array(fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary), { minLength: 1, maxLength: 20 }),
        async (userInputs) => {
          userRepository.clear();
          
          const createdUsers: User[] = [];
          const seenEmails = new Set<string>();
          
          for (const [email, password, name] of userInputs) {
            try {
              if (!seenEmails.has(email)) {
                const user = await authService.register({ email, password, name });
                createdUsers.push(user);
                seenEmails.add(email);
              } else {
                // Should fail for duplicate email
                await expect(authService.register({ email, password, name }))
                  .rejects.toThrow(ValidationError);
              }
            } catch (error) {
              // Skip validation errors during registration
              if (!(error instanceof ValidationError)) {
                throw error;
              }
            }
          }
          
          // All created users should have unique emails
          const userEmails = createdUsers.map(u => u.email);
          const uniqueEmails = new Set(userEmails);
          expect(uniqueEmails.size).toBe(userEmails.length);
        }
      ));
    });

    it('should maintain API key security invariant', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary, fc.array(permissionArbitrary, { minLength: 1, maxLength: 10 })),
        async ([email, password, name, keyPermissions]) => {
          userRepository.clear();
          apiKeyRepository.clear();
          
          try {
            // Register user
            const user = await authService.register({ email, password, name });
            
            // Create API keys
            const apiKeys: ApiKey[] = [];
            for (let i = 0; i < keyPermissions.length; i++) {
              const apiKey = await authService.createApiKey(user.id, {
                name: `Key ${i}`,
                permissions: keyPermissions[i]
              });
              apiKeys.push(apiKey);
            }
            
            // API key security invariants
            for (const apiKey of apiKeys) {
              // Raw key should never equal hashed key
              expect(apiKey.key).not.toBe(apiKey.hashedKey);
              
              // Should be able to validate with raw key
              const validated = await authService.validateApiKey(apiKey.key);
              expect(validated.id).toBe(apiKey.id);
              
              // Should not be able to validate with hashed key
              await expect(authService.validateApiKey(apiKey.hashedKey))
                .rejects.toThrow(AuthenticationError);
            }
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });

    it('should maintain permission consistency invariant', () => {
      fc.assert(fc.asyncProperty(
        fc.tuple(validEmailArbitrary, strongPasswordArbitrary, nameArbitrary, permissionArbitrary),
        async ([email, password, name, permissions]) => {
          userRepository.clear();
          apiKeyRepository.clear();
          
          try {
            // Register user
            const user = await authService.register({ email, password, name });
            
            // Initially should have no permissions (except admin users)
            if (user.role !== 'admin') {
              for (const permission of permissions) {
                const hasPermission = await authService.checkPermission(user.id, permission);
                expect(hasPermission).toBe(false);
              }
            }
            
            // Create API key with permissions
            await authService.createApiKey(user.id, {
              name: 'Test Key',
              permissions
            });
            
            // Now should have all the permissions
            for (const permission of permissions) {
              const hasPermission = await authService.checkPermission(user.id, permission);
              expect(hasPermission).toBe(true);
            }
          } catch (error) {
            // Skip validation errors during registration
            if (!(error instanceof ValidationError)) {
              throw error;
            }
          }
        }
      ));
    });
  });
});