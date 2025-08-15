import * as crypto from 'crypto';
import { z } from 'zod';

// Validation schemas
export const LoginRequest = z.object({
  email: z.string().email().max(255),
  password: z.string().min(8).max(128),
});

export const RegisterRequest = z.object({
  email: z.string().email().max(255),
  password: z.string().min(8).max(128).regex(/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]/),
  name: z.string().min(2).max(100),
});

export const ApiKeyRequest = z.object({
  name: z.string().min(1).max(100),
  permissions: z.array(z.string().min(1)).min(1),
});

export type LoginRequest = z.infer<typeof LoginRequest>;
export type RegisterRequest = z.infer<typeof RegisterRequest>;
export type ApiKeyRequest = z.infer<typeof ApiKeyRequest>;

// Domain entities
export interface User {
  id: string;
  email: string;
  name: string;
  passwordHash: string;
  role: string;
  isActive: boolean;
  createdAt: Date;
  lastLoginAt?: Date;
}

export interface ApiKey {
  id: string;
  name: string;
  key: string;
  hashedKey: string;
  permissions: string[];
  userId: string;
  isActive: boolean;
  createdAt: Date;
  lastUsedAt?: Date;
  expiresAt?: Date;
}

export interface JwtPayload {
  userId: string;
  email: string;
  role: string;
  iat: number;
  exp: number;
}

export interface AuthToken {
  token: string;
  type: 'jwt' | 'api_key';
  expiresAt: Date;
  user: Omit<User, 'passwordHash'>;
}

// Custom errors
export class AuthenticationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'AuthenticationError';
  }
}

export class AuthorizationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'AuthorizationError';
  }
}

export class ValidationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'ValidationError';
  }
}

export class RateLimitError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'RateLimitError';
  }
}

// Repository interfaces
export interface UserRepository {
  findByEmail(email: string): Promise<User | null>;
  findById(id: string): Promise<User | null>;
  create(user: Omit<User, 'id' | 'createdAt'>): Promise<User>;
  updateLastLogin(userId: string): Promise<void>;
  updatePassword(userId: string, passwordHash: string): Promise<void>;
}

export interface ApiKeyRepository {
  findByKey(hashedKey: string): Promise<ApiKey | null>;
  findByUserId(userId: string): Promise<ApiKey[]>;
  create(apiKey: Omit<ApiKey, 'id' | 'createdAt'>): Promise<ApiKey>;
  updateLastUsed(keyId: string): Promise<void>;
  revoke(keyId: string): Promise<void>;
}

// Rate limiting interface
export interface RateLimiter {
  checkLimit(identifier: string, operation: string): Promise<boolean>;
  getRemainingAttempts(identifier: string, operation: string): Promise<number>;
}

// Authentication service
export class AuthService {
  private readonly JWT_SECRET: string;
  private readonly JWT_EXPIRES_IN = '24h';
  private readonly API_KEY_LENGTH = 32;
  private readonly MAX_LOGIN_ATTEMPTS = 5;
  private readonly LOCKOUT_DURATION = 15 * 60 * 1000; // 15 minutes

  constructor(
    private userRepository: UserRepository,
    private apiKeyRepository: ApiKeyRepository,
    private rateLimiter: RateLimiter,
    jwtSecret?: string
  ) {
    this.JWT_SECRET = jwtSecret || process.env.JWT_SECRET || 'default-secret-key';
    if (this.JWT_SECRET === 'default-secret-key') {
      console.warn('Using default JWT secret. Set JWT_SECRET environment variable for production.');
    }
  }

  /**
   * Authenticate user with email and password
   */
  async login(request: LoginRequest): Promise<AuthToken> {
    // Validate input
    const parsed = LoginRequest.safeParse(request);
    if (!parsed.success) {
      throw new ValidationError('Invalid login credentials format');
    }

    const { email, password } = parsed.data;

    // Check rate limiting
    const canAttempt = await this.rateLimiter.checkLimit(email, 'login');
    if (!canAttempt) {
      throw new RateLimitError('Too many login attempts. Please try again later.');
    }

    // Find user
    const user = await this.userRepository.findByEmail(email);
    if (!user || !user.isActive) {
      throw new AuthenticationError('Invalid credentials');
    }

    // Verify password
    const isValidPassword = await this.verifyPassword(password, user.passwordHash);
    if (!isValidPassword) {
      throw new AuthenticationError('Invalid credentials');
    }

    // Update last login
    await this.userRepository.updateLastLogin(user.id);

    // Generate JWT token
    const token = this.generateJwtToken(user);
    const expiresAt = new Date(Date.now() + 24 * 60 * 60 * 1000); // 24 hours

    return {
      token,
      type: 'jwt',
      expiresAt,
      user: {
        id: user.id,
        email: user.email,
        name: user.name,
        role: user.role,
        isActive: user.isActive,
        createdAt: user.createdAt,
        lastLoginAt: user.lastLoginAt
      }
    };
  }

  /**
   * Register new user
   */
  async register(request: RegisterRequest): Promise<User> {
    // Validate input
    const parsed = RegisterRequest.safeParse(request);
    if (!parsed.success) {
      throw new ValidationError('Invalid registration data format');
    }

    const { email, password, name } = parsed.data;

    // Check if user exists
    const existingUser = await this.userRepository.findByEmail(email);
    if (existingUser) {
      throw new ValidationError('User with this email already exists');
    }

    // Hash password
    const passwordHash = await this.hashPassword(password);

    // Create user
    const newUser = await this.userRepository.create({
      email,
      name,
      passwordHash,
      role: 'user',
      isActive: true,
      lastLoginAt: undefined
    });

    return newUser;
  }

  /**
   * Validate JWT token
   */
  async validateJwtToken(token: string): Promise<User> {
    try {
      const payload = this.verifyJwtToken(token) as JwtPayload;
      
      const user = await this.userRepository.findById(payload.userId);
      if (!user || !user.isActive) {
        throw new AuthenticationError('Invalid token');
      }

      return user;
    } catch (error) {
      throw new AuthenticationError('Invalid token');
    }
  }

  /**
   * Create API key for user
   */
  async createApiKey(userId: string, request: ApiKeyRequest): Promise<ApiKey> {
    // Validate input
    const parsed = ApiKeyRequest.safeParse(request);
    if (!parsed.success) {
      throw new ValidationError('Invalid API key request format');
    }

    const { name, permissions } = parsed.data;

    // Verify user exists
    const user = await this.userRepository.findById(userId);
    if (!user || !user.isActive) {
      throw new AuthenticationError('User not found');
    }

    // Generate API key
    const key = this.generateApiKey();
    const hashedKey = await this.hashApiKey(key);

    // Create API key record
    const apiKey = await this.apiKeyRepository.create({
      name,
      key, // Store plain key for return (will be shown only once)
      hashedKey,
      permissions,
      userId,
      isActive: true,
      lastUsedAt: undefined,
      expiresAt: undefined
    });

    return apiKey;
  }

  /**
   * Validate API key
   */
  async validateApiKey(key: string): Promise<ApiKey> {
    const hashedKey = await this.hashApiKey(key);
    
    const apiKey = await this.apiKeyRepository.findByKey(hashedKey);
    if (!apiKey || !apiKey.isActive) {
      throw new AuthenticationError('Invalid API key');
    }

    if (apiKey.expiresAt && apiKey.expiresAt < new Date()) {
      throw new AuthenticationError('API key expired');
    }

    // Update last used timestamp
    await this.apiKeyRepository.updateLastUsed(apiKey.id);

    return apiKey;
  }

  /**
   * Check if user has permission
   */
  async checkPermission(userId: string, permission: string): Promise<boolean> {
    const user = await this.userRepository.findById(userId);
    if (!user || !user.isActive) {
      return false;
    }

    // Admin role has all permissions
    if (user.role === 'admin') {
      return true;
    }

    // Check user-specific permissions through API keys
    const apiKeys = await this.apiKeyRepository.findByUserId(userId);
    const activeKeys = apiKeys.filter(key => key.isActive);
    
    return activeKeys.some(key => key.permissions.includes(permission));
  }

  /**
   * Revoke API key
   */
  async revokeApiKey(keyId: string): Promise<void> {
    await this.apiKeyRepository.revoke(keyId);
  }

  /**
   * Change user password
   */
  async changePassword(userId: string, currentPassword: string, newPassword: string): Promise<void> {
    const user = await this.userRepository.findById(userId);
    if (!user || !user.isActive) {
      throw new AuthenticationError('User not found');
    }

    // Verify current password
    const isValidPassword = await this.verifyPassword(currentPassword, user.passwordHash);
    if (!isValidPassword) {
      throw new AuthenticationError('Current password is incorrect');
    }

    // Validate new password
    const passwordValidation = z.string().min(8).regex(/^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]/).safeParse(newPassword);
    if (!passwordValidation.success) {
      throw new ValidationError('New password does not meet security requirements');
    }

    // Hash and update password
    const newPasswordHash = await this.hashPassword(newPassword);
    await this.userRepository.updatePassword(userId, newPasswordHash);
  }

  // Private helper methods
  private async hashPassword(password: string): Promise<string> {
    return new Promise((resolve, reject) => {
      const salt = crypto.randomBytes(16).toString('hex');
      crypto.pbkdf2(password, salt, 100000, 64, 'sha512', (err, derivedKey) => {
        if (err) reject(err);
        resolve(salt + ':' + derivedKey.toString('hex'));
      });
    });
  }

  private async verifyPassword(password: string, hash: string): Promise<boolean> {
    return new Promise((resolve, reject) => {
      const [salt, key] = hash.split(':');
      crypto.pbkdf2(password, salt, 100000, 64, 'sha512', (err, derivedKey) => {
        if (err) reject(err);
        resolve(key === derivedKey.toString('hex'));
      });
    });
  }

  private generateJwtToken(user: User): string {
    const payload: Omit<JwtPayload, 'iat' | 'exp'> = {
      userId: user.id,
      email: user.email,
      role: user.role
    };

    // Simple JWT implementation (in production, use a proper library like jsonwebtoken)
    const header = Buffer.from(JSON.stringify({ alg: 'HS256', typ: 'JWT' })).toString('base64url');
    const now = Math.floor(Date.now() / 1000);
    const fullPayload = { ...payload, iat: now, exp: now + (24 * 60 * 60) };
    const payloadB64 = Buffer.from(JSON.stringify(fullPayload)).toString('base64url');
    
    const signature = crypto
      .createHmac('sha256', this.JWT_SECRET)
      .update(`${header}.${payloadB64}`)
      .digest('base64url');

    return `${header}.${payloadB64}.${signature}`;
  }

  private verifyJwtToken(token: string): JwtPayload {
    const [header, payload, signature] = token.split('.');
    
    // Verify signature
    const expectedSignature = crypto
      .createHmac('sha256', this.JWT_SECRET)
      .update(`${header}.${payload}`)
      .digest('base64url');

    if (signature !== expectedSignature) {
      throw new Error('Invalid signature');
    }

    // Decode payload
    const decodedPayload = JSON.parse(Buffer.from(payload, 'base64url').toString());
    
    // Check expiration
    if (decodedPayload.exp < Math.floor(Date.now() / 1000)) {
      throw new Error('Token expired');
    }

    return decodedPayload as JwtPayload;
  }

  private generateApiKey(): string {
    return crypto.randomBytes(this.API_KEY_LENGTH).toString('hex');
  }

  private async hashApiKey(key: string): Promise<string> {
    return crypto.createHash('sha256').update(key).digest('hex');
  }
}