# Cache verification security specification

This fixture uses explicit `SEC-CLAIM:` blocks so the MVP extractor remains deterministic and does not call external LLMs.

## Verification cache

SEC-CLAIM:
id: SEC-CLAIM-101
type: invariant
criticality: high
targetLevel: A2
statement: Cache key must include all attacker-controlled fields that affect the verification result.
stride: Tampering
cwe: CWE-20
sourceUri: fixtures/security-assurance/extract-claims/spec.md
sourceSection: Verification cache
boundaryIds: TB-001
entryPoints: api, p2p
attackerControlled: true
dataClasses: verification-input
requiredLanes: spec, adversarial, behavior
notes: Fixture claim for deterministic Security Assurance Lane extraction.

## Token lifetime

SEC-CLAIM:
type: precondition
criticality: medium
targetLevel: A1
statement: Token validation must reject expired bearer tokens before granting access to protected resources.
stride: Spoofing, Elevation of Privilege
cwe: CWE-287, CWE-613
sourceUri: fixtures/security-assurance/extract-claims/spec.md
sourceSection: Token lifetime
boundaryIds: TB-API
entryPoints: api
dataClasses: bearer-token
requiredLanes: spec, behavior
