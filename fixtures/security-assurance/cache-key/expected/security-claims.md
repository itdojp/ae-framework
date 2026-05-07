# Security claim extraction summary

- Generated at: 2026-05-07T00:00:00.000Z
- Source: fixtures/security-assurance/cache-key/inputs/spec.md
- Claims: 3
- Warnings: 0

## Claims

- `SEC-CLAIM-001` (high): Cache key must include tenant, subject, and attacker-controlled scope fields that affect authorization.
- `SEC-CLAIM-002` (medium): Bearer token validation must reject expired tokens before cache lookup.
- `SEC-CLAIM-003` (low): Test-only fixture cache helpers must remain outside the production audit scope and trust boundary.

## Warnings

- None
