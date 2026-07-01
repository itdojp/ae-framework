# Domain Assurance Preset: Web API / BFF structured assurance preset

- presetId: `web-api-bff`
- generatedAt: `2026-07-01T00:00:00.000Z`
- classification: `structured-assurance`
- reportOnly: `true`
- startingCommand: `pnpm run verify:lite`

## Target user

API or BFF maintainers who need stable PR quality, request/response contract traceability, and a low-friction path from Issue to assurance review.

## Recommended when

- The change modifies externally visible HTTP or BFF contracts.
- Reviewers need to connect requirements, OpenAPI or route contracts, tests, and PR evidence.
- The team can retain CI artifacts and run the reference flow locally.

## Not recommended when

- The change is a short-lived one-off script with no retained API contract.
- There is no CI or artifact retention path for verification evidence.
- The route only needs high-level prose review and no executable check.

## Required inputs

| ID | Input | Path pattern | Contract |
| --- | --- | --- | --- |
| requirement | Requirement or Issue summary | docs/getting-started/REFERENCE-FLOW.md or spec/requirements/*.md | n/a |
| api-contract | HTTP contract or route specification | spec/openapi/**/*.yaml or docs/api/**/*.md | OpenAPI or project-local API contract |
| context-pack | Context Pack and Boundary Map | spec/context-pack/**/*.{json,yaml,yml} | context-pack/v1 + context-pack-boundary-map/v1 |
| exec-plan | ExecPlan v2 | artifacts/plan/exec-plan.v2.json or fixtures/exec-plan/*.json | exec-plan/v2 |

## Verification commands

| ID | Command | Purpose |
| --- | --- | --- |
| context-pack-validate | `pnpm run context-pack:validate` | Validate the design SSOT before executing API/BFF implementation work. |
| boundary-map | `pnpm run context-pack:verify-boundary-map` | Confirm route/controller/data-access ownership boundaries and dependency edges. |
| exec-plan-validate | `pnpm run exec-plan:v2:validate -- --file artifacts/plan/exec-plan.v2.json` | Check that tasks, commands, evidence requirements, and rollback are reviewable. |
| review-surface | `pnpm run assurance:review-surface` | Render a PR-facing assurance review surface after evidence artifacts exist. |

## Expected artifacts

| ID | Path | Required | Review purpose |
| --- | --- | --- | --- |
| verify-lite-summary | artifacts/verify-lite/verify-lite-run-summary.json | yes | Shows whether the default local verification lane passed. |
| boundary-map-report | artifacts/context-pack/context-pack-boundary-map-report.json | yes | Shows whether API/BFF ownership and dependency boundaries match the Context Pack. |
| exec-plan-v2 | artifacts/plan/exec-plan.v2.json | yes | Links implementation tasks, validation commands, output artifacts, and rollback. |
| assurance-review | artifacts/review/assurance-review.md | no | Human-readable PR surface for claim/evidence inspection. |

## Escalation rule

- trigger: Escalate when the route handles authentication, authorization, payment, PII, cross-service contract breakage, or a policy `risk:high` label.
- action: Add security or high-assurance lanes, require human maintainer approval, and keep policy-gate enforcement changes in a separate policy issue.
- human decision required: yes

## Reused contracts

- context-pack/v1
- context-pack-boundary-map/v1
- exec-plan/v2
- verify-lite-run-summary/v1
- claim-evidence-manifest/v1
- assurance-summary/v1

## Boundaries

- Domain presets select inputs, commands, and evidence surfaces; they do not approve, merge, or change policy-gate enforcement.
- No live external APIs were called.
