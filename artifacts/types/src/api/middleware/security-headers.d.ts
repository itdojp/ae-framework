/**
 * Security Headers Middleware
 * Implements basic HTTP security headers for the AE-Framework API
 */
import { FastifyInstance } from 'fastify';
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
/**
 * Fastify plugin for security headers
 */
export declare function securityHeadersPlugin(fastify: FastifyInstance, options?: SecurityHeadersOptions): Promise<void>;
/**
 * Environment-specific security configurations
 */
export declare const securityConfigurations: {
    development: SecurityHeadersOptions;
    testing: SecurityHeadersOptions;
    production: SecurityHeadersOptions;
};
/**
 * Get security configuration for current environment
 */
export declare function getSecurityConfiguration(environment?: string): SecurityHeadersOptions;
export default securityHeadersPlugin;
