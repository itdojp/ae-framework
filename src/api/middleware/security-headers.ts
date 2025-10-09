/**
 * Security Headers Middleware
 * Implements basic HTTP security headers for the AE-Framework API
 */

import type { FastifyInstance, FastifyRequest, FastifyReply } from 'fastify';
import fp from 'fastify-plugin';

export interface SecurityHeadersOptions {
  /** Enable/disable all security headers */
  enabled?: boolean;
  
  /** Content Security Policy */
  contentSecurityPolicy?: {
    enabled?: boolean;
    directives?: string;
  };
  
  /** X-Frame-Options */
  frameOptions?: {
    enabled?: boolean;
    value?: 'DENY' | 'SAMEORIGIN' | string;
  };
  
  /** X-Content-Type-Options */
  contentTypeOptions?: {
    enabled?: boolean;
  };
  
  /** Referrer-Policy */
  referrerPolicy?: {
    enabled?: boolean;
    value?: string;
  };
  
  /** Strict-Transport-Security */
  strictTransportSecurity?: {
    enabled?: boolean;
    maxAge?: number;
    includeSubDomains?: boolean;
    preload?: boolean;
  };
  
  /** X-XSS-Protection */
  xssProtection?: {
    enabled?: boolean;
    value?: string;
  };
  
  /** Permissions-Policy */
  permissionsPolicy?: {
    enabled?: boolean;
    directives?: string;
  };
}

const DEFAULT_OPTIONS: Required<SecurityHeadersOptions> = {
  enabled: true,
  contentSecurityPolicy: {
    enabled: true,
    directives: "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; img-src 'self' data: https:; font-src 'self'; connect-src 'self'; frame-ancestors 'none';"
  },
  frameOptions: {
    enabled: true,
    value: 'DENY'
  },
  contentTypeOptions: {
    enabled: true
  },
  referrerPolicy: {
    enabled: true,
    value: 'strict-origin-when-cross-origin'
  },
  strictTransportSecurity: {
    enabled: true,
    maxAge: 31536000, // 1 year
    includeSubDomains: true,
    preload: false
  },
  xssProtection: {
    enabled: true,
    value: '1; mode=block'
  },
  permissionsPolicy: {
    enabled: true,
    directives: 'camera=(), microphone=(), geolocation=(), payment=(), usb=(), magnetometer=(), gyroscope=(), accelerometer=()'
  }
};

/**
 * Generate HSTS header value
 */
function generateHSTSValue(options: Required<SecurityHeadersOptions>['strictTransportSecurity']): string {
  let value = `max-age=${options.maxAge}`;
  
  if (options.includeSubDomains) {
    value += '; includeSubDomains';
  }
  
  if (options.preload) {
    value += '; preload';
  }
  
  return value;
}

/**
 * Security headers hook function
 */
function securityHeadersHook(
  request: FastifyRequest,
  reply: FastifyReply,
  options: Required<SecurityHeadersOptions>
): void {
  if (!options.enabled) {
    return;
  }

  // Content Security Policy
  if (options.contentSecurityPolicy.enabled && options.contentSecurityPolicy.directives) {
    reply.header('Content-Security-Policy', options.contentSecurityPolicy.directives);
  }

  // X-Frame-Options
  if (options.frameOptions.enabled) {
    reply.header('X-Frame-Options', options.frameOptions.value);
  }

  // X-Content-Type-Options
  if (options.contentTypeOptions.enabled) {
    reply.header('X-Content-Type-Options', 'nosniff');
  }

  // Referrer-Policy
  if (options.referrerPolicy.enabled && options.referrerPolicy.value) {
    reply.header('Referrer-Policy', options.referrerPolicy.value);
  }

  // Strict-Transport-Security (only for HTTPS)
  if (options.strictTransportSecurity.enabled && request.protocol === 'https') {
    const hstsValue = generateHSTSValue(options.strictTransportSecurity);
    reply.header('Strict-Transport-Security', hstsValue);
  }

  // X-XSS-Protection (deprecated but still useful for older browsers)
  if (options.xssProtection.enabled && options.xssProtection.value) {
    reply.header('X-XSS-Protection', options.xssProtection.value);
  }

  // Permissions-Policy
  if (options.permissionsPolicy.enabled && options.permissionsPolicy.directives) {
    reply.header('Permissions-Policy', options.permissionsPolicy.directives);
  }

  // Remove server identification
  reply.removeHeader('x-powered-by');
  reply.removeHeader('server');
}

/**
 * Fastify plugin for security headers
 */
export const securityHeadersPlugin = fp(async (
  fastify: FastifyInstance,
  options: SecurityHeadersOptions = {}
) => {
  const finalOptions = { ...DEFAULT_OPTIONS, ...options } as Required<SecurityHeadersOptions>;

  // Merge nested options
  (Object.keys(finalOptions) as (keyof SecurityHeadersOptions)[]).forEach(key => {
    const baseValue = finalOptions[key];
    const overrideValue = options[key];

    if (baseValue && typeof baseValue === 'object' && overrideValue && typeof overrideValue === 'object') {
      finalOptions[key] = {
        ...(baseValue as Record<string, any>),
        ...(overrideValue as Record<string, any>)
      } as any;
    }
  });

  fastify.addHook('onSend', (request, reply, payload, done) => {
    securityHeadersHook(request, reply, finalOptions);
    done(null, payload);
  });
}, { name: 'security-headers-plugin' });

/**
 * Environment-specific security configurations
 */
export const securityConfigurations = {
  development: {
    enabled: true,
    contentSecurityPolicy: {
      enabled: true,
      // NOTE: Development CSP allows 'unsafe-inline' and 'unsafe-eval' for convenience.
      // In production, consider using nonces or hashes instead to maintain better security.
      // Example: "script-src 'self' 'nonce-<RANDOM_NONCE>'; style-src 'self' 'nonce-<RANDOM_NONCE>'"
      directives: "default-src 'self' 'unsafe-inline' 'unsafe-eval'; script-src 'self' 'unsafe-inline' 'unsafe-eval'; style-src 'self' 'unsafe-inline'; img-src 'self' data: https:; font-src 'self'; connect-src 'self' ws: wss:; frame-ancestors 'none';"
    },
    strictTransportSecurity: {
      enabled: false // Usually disabled in development over HTTP
    }
  } as SecurityHeadersOptions,

  testing: {
    enabled: true,
    contentSecurityPolicy: {
      enabled: false // Often disabled for easier testing
    },
    strictTransportSecurity: {
      enabled: false
    }
  } as SecurityHeadersOptions,

  production: {
    enabled: true,
    contentSecurityPolicy: {
      enabled: true,
      directives: "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data: https:; font-src 'self'; connect-src 'self'; frame-ancestors 'none'; form-action 'self'; base-uri 'self';"
    },
    frameOptions: {
      enabled: true,
      value: 'DENY'
    },
    strictTransportSecurity: {
      enabled: true,
      maxAge: 31536000,
      includeSubDomains: true,
      preload: true
    },
    permissionsPolicy: {
      enabled: true,
      directives: 'camera=(), microphone=(), geolocation=(), payment=(), usb=(), magnetometer=(), gyroscope=(), accelerometer=(), fullscreen=(), autoplay=()'
    }
  } as SecurityHeadersOptions
};

/**
 * Get security configuration for current environment
 */
export function getSecurityConfiguration(environment?: string): SecurityHeadersOptions {
  const env = environment || process.env['NODE_ENV'] || 'development';
  
  switch (env) {
    case 'production':
      return securityConfigurations.production;
    case 'test':
    case 'testing':
      return securityConfigurations.testing;
    case 'development':
    default:
      return securityConfigurations.development;
  }
}

export default securityHeadersPlugin;
