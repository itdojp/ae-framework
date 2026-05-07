# Security proof-attempt audit summary

- Generated at: 2026-05-07T00:00:00.000Z
- Audit tasks: 3
- Ready tasks: 3
- Blocked tasks: 0
- Candidate locations: 7
- Findings generated: 2
- No-finding responses: 1
- Warnings: 0

## Audit tasks

### SEC-AUDIT-TASK-001 / SEC-CLAIM-001

- Status: ready
- Candidate locations: 2

Proof-attempt prompt:
- Map: Map the security claim to these candidate code paths: - src/cache.ts:13-20 (buildCacheKey): Matched security claim terms in buildCacheKey: attacker, authorization, cache, controlled, key, scope, security, subject. - src/cache.ts:25-31 (lookupVerificationCache): Matched security claim terms in lookupVerificationCache: cache, key, verification.
- Prove: Prove whether the implementation satisfies claim SEC-CLAIM-001: Cache key must include tenant, subject, and attacker-controlled scope fields that affect authorization.
- Stress-Test: Stress-test attacker-controlled inputs, trust-boundary assumptions, cache/key equivalence classes, and edge cases that could break the proof. Do not generate exploit automation.
- Report: Report a candidate finding only when the proof fails with concrete code evidence. Keep all findings as candidate status until three-gate review.

Candidate locations:
- `src/cache.ts:13-20 (buildCacheKey)`: Matched security claim terms in buildCacheKey: attacker, authorization, cache, controlled, key, scope, security, subject.
- `src/cache.ts:25-31 (lookupVerificationCache)`: Matched security claim terms in lookupVerificationCache: cache, key, verification.

### SEC-AUDIT-TASK-002 / SEC-CLAIM-002

- Status: ready
- Candidate locations: 3

Proof-attempt prompt:
- Map: Map the security claim to these candidate code paths: - src/cache.ts:25-31 (lookupVerificationCache): Matched security claim terms in lookupVerificationCache: bearer, cache, key, lookup, token. - src/cache.ts:13-20 (buildCacheKey): Matched security claim terms in buildCacheKey: cache, key, security. - src/cache.ts:21-24 (isFreshToken): Matched security claim terms in isFreshToken: bearer, token.
- Prove: Prove whether the implementation satisfies claim SEC-CLAIM-002: Bearer token validation must reject expired tokens before cache lookup.
- Stress-Test: Stress-test attacker-controlled inputs, trust-boundary assumptions, cache/key equivalence classes, and edge cases that could break the proof. Do not generate exploit automation.
- Report: Report a candidate finding only when the proof fails with concrete code evidence. Keep all findings as candidate status until three-gate review.

Candidate locations:
- `src/cache.ts:25-31 (lookupVerificationCache)`: Matched security claim terms in lookupVerificationCache: bearer, cache, key, lookup, token.
- `src/cache.ts:13-20 (buildCacheKey)`: Matched security claim terms in buildCacheKey: cache, key, security.
- `src/cache.ts:21-24 (isFreshToken)`: Matched security claim terms in isFreshToken: bearer, token.

### SEC-AUDIT-TASK-003 / SEC-CLAIM-003

- Status: ready
- Candidate locations: 2

Proof-attempt prompt:
- Map: Map the security claim to these candidate code paths: - src/cache.ts:13-20 (buildCacheKey): Matched security claim terms in buildCacheKey: cache, fixture, input, key, scope, security. - src/cache.ts:25-31 (lookupVerificationCache): Matched security claim terms in lookupVerificationCache: cache, input, key.
- Prove: Prove whether the implementation satisfies claim SEC-CLAIM-003: Test-only fixture cache helpers must remain outside the production audit scope and trust boundary.
- Stress-Test: Stress-test attacker-controlled inputs, trust-boundary assumptions, cache/key equivalence classes, and edge cases that could break the proof. Do not generate exploit automation.
- Report: Report a candidate finding only when the proof fails with concrete code evidence. Keep all findings as candidate status until three-gate review.

Candidate locations:
- `src/cache.ts:13-20 (buildCacheKey)`: Matched security claim terms in buildCacheKey: cache, fixture, input, key, scope, security.
- `src/cache.ts:25-31 (lookupVerificationCache)`: Matched security claim terms in lookupVerificationCache: cache, input, key.

## Claim audit statuses

- SEC-AUDIT-TASK-001 / SEC-CLAIM-001: finding (SEC-FINDING-001) — The simulated proof attempt cannot establish that all attacker-controlled authorization fields participate in cache-key material.
- SEC-AUDIT-TASK-002 / SEC-CLAIM-002: no-finding — isFreshToken rejects tokens whose expiresAtEpochMs is not greater than the current time before cache lookup.
- SEC-AUDIT-TASK-003 / SEC-CLAIM-003: finding (SEC-FINDING-002) — The simulated proof attempt reports a test-only helper that resembles production cache-key construction.

## Findings

- SEC-FINDING-001 / SEC-CLAIM-001: Authorization cache key omits attacker-controlled scope (high, candidate)
- SEC-FINDING-002 / SEC-CLAIM-003: Test fixture cache helper resembles production key construction (low, candidate)

## Warnings

- None
