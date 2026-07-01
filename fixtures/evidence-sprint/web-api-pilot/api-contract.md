# Web API Pilot Contract Fixture: Evidence Sprint pilot evidence summary

This fixture is the API-contract evidence for Issue #3572. It is a
report-only, deterministic Web API pilot contract; no runtime route is added by
this PR.

## Selected small API change

Introduce a read-only evidence summary endpoint for an internal assurance UI or
BFF:

```http
GET /internal/evidence-sprint/pilots/{pilotId}
```

The selected pilot id is `evidence-011-web-api-pilot`.

## Request contract

| Field | Location | Required | Rule |
| --- | --- | --- | --- |
| `pilotId` | path | yes | Must equal `evidence-011-web-api-pilot` for this fixture. |
| `Accept` | header | yes | `application/json` |

## Response contract

### `200 OK`

```json
{
  "pilotId": "evidence-011-web-api-pilot",
  "status": "completed",
  "reportOnly": true,
  "domainPreset": "web-api-bff",
  "artifacts": [
    {
      "id": "api-contract",
      "kind": "api-contract",
      "path": "fixtures/evidence-sprint/web-api-pilot/api-contract.md"
    },
    {
      "id": "domain-preset-report",
      "kind": "domain-assurance-preset-report/v1",
      "path": "fixtures/evidence-sprint/web-api-pilot/domain-preset-report.json"
    },
    {
      "id": "measurement-report",
      "kind": "evidence-sprint-measurement-report/v1",
      "path": "fixtures/evidence-sprint/web-api-pilot/measurement-report.json"
    }
  ],
  "claimBoundary": "traceability and instrumentation readiness only"
}
```

### `404 Not Found`

```json
{
  "error": "pilot_not_found",
  "message": "No report-only Evidence Sprint pilot exists for the requested pilotId."
}
```

## Contract invariants

- The endpoint is read-only and must not mutate repository, CI, PR, or Issue
  state.
- The endpoint must not expose raw review comments, private pilot data, secrets,
  credentials, PII, or exact private timestamps.
- `reportOnly` must remain `true`; the response is not approval, waiver, merge
  authority, or policy-gate enforcement.
- Public claims from this endpoint are limited to the scoped pilot evidence
  chain and metric collection readiness.

## Escalation rule

Escalate to human maintainer review and security/high-assurance lanes before
implementation if a future live route handles authentication, authorization,
payment, PII, cross-service contract breakage, or a `risk:high` policy label.
