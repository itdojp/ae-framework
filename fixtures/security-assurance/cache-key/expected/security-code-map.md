# Security code-map summary

- Generated at: 2026-05-07T00:00:00.000Z
- Claims: 3
- Mapped claims: 3
- Candidate locations: 7
- Warnings: 0

## Mappings

### SEC-CLAIM-001

- Coverage: partial
- Candidate locations: 2

- `src/cache.ts:13-20` (buildCacheKey): Matched security claim terms in buildCacheKey: attacker, authorization, cache, controlled, key, scope, security, subject.
- `src/cache.ts:25-31` (lookupVerificationCache): Matched security claim terms in lookupVerificationCache: cache, key, verification.

### SEC-CLAIM-002

- Coverage: partial
- Candidate locations: 3

- `src/cache.ts:25-31` (lookupVerificationCache): Matched security claim terms in lookupVerificationCache: bearer, cache, key, lookup, token.
- `src/cache.ts:13-20` (buildCacheKey): Matched security claim terms in buildCacheKey: cache, key, security.
- `src/cache.ts:21-24` (isFreshToken): Matched security claim terms in isFreshToken: bearer, token.

### SEC-CLAIM-003

- Coverage: partial
- Candidate locations: 2

- `src/cache.ts:13-20` (buildCacheKey): Matched security claim terms in buildCacheKey: cache, fixture, input, key, scope, security.
- `src/cache.ts:25-31` (lookupVerificationCache): Matched security claim terms in lookupVerificationCache: cache, input, key.

## Document warnings

- None
