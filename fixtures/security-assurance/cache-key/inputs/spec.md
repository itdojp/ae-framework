# Cache key Security Assurance fixture

この fixture は Security Assurance Lane の end-to-end golden scenario 用の小さな TypeScript 対象です。`SEC-CLAIM:` ブロックは extractor MVP が外部 LLM を使わず決定的に処理できる形式に固定しています。

## Verification cache key

SEC-CLAIM:
id: SEC-CLAIM-001
type: invariant
criticality: high
targetLevel: A2
statement: Cache key must include tenant, subject, and attacker-controlled scope fields that affect authorization.
stride: Tampering
cwe: CWE-20
sourceUri: fixtures/security-assurance/cache-key/inputs/spec.md
sourceSection: Verification cache key
boundaryIds: TB-CACHE
entryPoints: api
attackerControlled: true
dataClasses: tenant, subject, scope, authorization-context
requiredLanes: spec, adversarial
notes: Fixture intentionally leaves scope out of buildCacheKey so the audit stage emits one candidate finding.

## Bearer token freshness

SEC-CLAIM:
id: SEC-CLAIM-002
type: precondition
criticality: medium
targetLevel: A1
statement: Bearer token validation must reject expired tokens before cache lookup.
stride: Spoofing
cwe: CWE-613
sourceUri: fixtures/security-assurance/cache-key/inputs/spec.md
sourceSection: Bearer token freshness
boundaryIds: TB-CACHE
entryPoints: api
attackerControlled: true
dataClasses: bearer-token
requiredLanes: spec
notes: Fixture response marks this claim as no-finding.

## Test fixture isolation

SEC-CLAIM:
id: SEC-CLAIM-003
type: assumption
criticality: low
targetLevel: A1
statement: Test-only fixture cache helpers must remain outside the production audit scope and trust boundary.
stride: Repudiation
cwe: CWE-693
sourceUri: fixtures/security-assurance/cache-key/inputs/spec.md
sourceSection: Test fixture isolation
boundaryIds: TB-TEST
entryPoints: test-fixture
attackerControlled: false
dataClasses: fixture-input
requiredLanes: spec, adversarial
notes: Fixture response reports a test-only helper that the three-gate review must classify out-of-scope.
