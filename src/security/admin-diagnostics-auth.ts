import { timingSafeEqual } from 'node:crypto';
import type { FastifyReply, FastifyRequest } from 'fastify';

export interface AdminDiagnosticsAuthOptions {
  token?: string;
}

const normalizeToken = (value: unknown): string => (typeof value === 'string' ? value.trim() : '');

const configuredAdminToken = (options: AdminDiagnosticsAuthOptions = {}): string =>
  normalizeToken(options.token || process.env['AE_ADMIN_TOKEN'] || process.env['AE_DIAGNOSTICS_ADMIN_TOKEN']);

const firstHeaderValue = (value: string | string[] | undefined): string => {
  if (Array.isArray(value)) {
    return normalizeToken(value[0]);
  }
  return normalizeToken(value);
};

const extractCredential = (request: FastifyRequest): string => {
  const headerToken = firstHeaderValue(request.headers['x-ae-admin-token']);
  if (headerToken) {
    return headerToken;
  }

  const authorization = firstHeaderValue(request.headers.authorization);
  const match = authorization.match(/^Bearer\s+(.+)$/i);
  return normalizeToken(match?.[1]);
};

const constantTimeEquals = (actual: string, expected: string): boolean => {
  if (!actual || !expected) return false;
  const actualBuffer = Buffer.from(actual);
  const expectedBuffer = Buffer.from(expected);
  if (actualBuffer.length !== expectedBuffer.length) return false;
  return timingSafeEqual(actualBuffer, expectedBuffer);
};

export const requireAdminDiagnosticsAuth = (
  request: FastifyRequest,
  reply: FastifyReply,
  options: AdminDiagnosticsAuthOptions = {},
): boolean => {
  const expectedToken = configuredAdminToken(options);
  if (!expectedToken) {
    reply.code(403).send({
      error: 'DIAGNOSTICS_DISABLED',
      message: 'Detailed diagnostics require an admin diagnostics token.',
    });
    return false;
  }

  if (!constantTimeEquals(extractCredential(request), expectedToken)) {
    reply
      .header('www-authenticate', 'Bearer realm="ae-framework diagnostics"')
      .code(401)
      .send({
        error: 'UNAUTHORIZED',
        message: 'Admin credentials are required for diagnostics.',
      });
    return false;
  }

  return true;
};
