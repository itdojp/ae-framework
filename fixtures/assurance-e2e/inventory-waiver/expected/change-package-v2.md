## Change Package
- schema: `change-package/v2`
- generatedAt: 2026-05-06T00:00:00.000Z
- policy: `policy/risk-policy.yml`

### Intent
- Freeze an end-to-end assurance fixture for inventory reservation controls.

### Scope
- changed files: 2
- areas: assurance, test

### Risk
- selected: risk:low
- inferred: risk:low
- isHighRisk: false
- required labels: (none)
- missing required labels: (none)
- high-risk path matches: (none)
- force-high triggers: (none)

### Evidence
- present/missing: 2/0

| id | path | present |
| --- | --- | --- |
| verifyLiteSummary | `artifacts/verify-lite/verify-lite-run-summary.json` | yes |
| policyGateSummary | `artifacts/ci/policy-gate-summary.json` | yes |

### Proof-carrying Assurance
- evidence package: `artifacts/assurance-e2e/inventory-waiver/change-package-v2.json`
- target/achieved/status: A3/A2/partial
- claim states: satisfied=0, tested=0, model-checked=1, proved=0, runtime-mitigated=0, waived=1, unresolved=0, failed=0, not-applicable=0
- policy decision: unassessed (unknown, enforced=false)
- changed requirement refs: REQ-INV-001, REQ-INV-002

### Claims
| id | status | target | achieved | criticality | requirements | artifactRefs | statement |
| --- | --- | --- | --- | --- | --- | --- | --- |
| no-negative-balance | model-checked | A3 | A2 | high | REQ-INV-001 | 2 | Ledger balance never becomes negative after reservation settlement. |
| manual-fraud-review | waived | A3 | A2 | medium | REQ-INV-002 | 1 | High-risk reservations receive manual fraud review until model validation is complete. |

### Proof Obligations
| id | claimId | method | status | artifactRefs |
| --- | --- | --- | --- | --- |
| obl-no-negative-balance | no-negative-balance | tla | discharged | 1 |

### Validation Lanes
| id | status | evidenceRefs |
| --- | --- | --- |
| verifyLiteSummary | pass | 1 |
| policyGateSummary | pass | 1 |

### Release / Post-deploy Controls
- pre-deploy checks: 2
- post-deploy checks: post-deploy-verify workflow or release verification artifact required before production rollout
- rollback signals: golden-artifact-drift, post-deploy-verify.status=fail

### Residual Risks
| id | severity | claimIds | statement |
| --- | --- | --- | --- |
| claim:manual-fraud-review:waived | medium | manual-fraud-review | waived claim requires human review: High-risk reservations receive manual fraud review until model validation is complete. |

### Waivers
| owner | expires | relatedClaimIds | evidenceRefs | reason |
| --- | --- | --- | --- | --- |
| @team-risk | 2099-12-31 | manual-fraud-review | 1 | Manual fraud review is active while automated model validation evidence is being collected. |

### Reproducibility
- `pnpm -s run assurance:e2e -- --scenario inventory-waiver`
- `node scripts/ci/validate-json.mjs`

### Rollout Plan
- strategy: fixture-only-golden-regression
- This fixture does not change production runtime behavior.

### Monitoring Plan
- signals: assurance-e2e.diff, claim-evidence.summary, policy-gate.assurance.result
- alerts: golden-artifact-drift

### Exceptions
- (none)
