# Security Assurance fixture summary

- Scenario: cache-key
- Generated at: 2026-05-07T00:00:00.000Z
- Claims: 3
- Threats: 3
- Code-map candidate locations: 7
- Audit responses: finding=2, no-finding=1
- Findings: 2
- Review results: needs-human-review=1, rejected=0, out-of-scope=1
- Assurance claims: 3
- Manifest security: findings=2, highOrCriticalOpen=1, outOfScope=1, rejected=0

## Expected lane behavior

- `SEC-CLAIM-001` produces `SEC-FINDING-001` and remains `needs-human-review`.
- `SEC-CLAIM-002` has a `no-finding` proof-attempt response.
- `SEC-CLAIM-003` produces `SEC-FINDING-002`, which the Scope gate classifies as `out-of-scope`.
