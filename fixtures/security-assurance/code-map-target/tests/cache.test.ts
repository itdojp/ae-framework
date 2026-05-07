import { buildCacheKey } from '../src/cache.js';

export function testCacheKey(): string {
  return buildCacheKey({ userId: 'u1', resourceId: 'r1', verificationResult: 'allow' });
}
