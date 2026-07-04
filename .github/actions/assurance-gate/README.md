# ae-framework Assurance Gate action

Composite action for deploy-time profile selection. It validates a profile, reads assurance evidence from the consumer repository, evaluates the release policy with `@ae-framework/core`, and writes review-surface artifacts.

## Inputs

- `profile` (default: `minimal`): `minimal`, `standard`, `full`, or a custom profile YAML path in the consumer repository.
- `artifacts-dir` (default: `artifacts`): directory containing assurance artifacts and optional `evidence.json`.
- `policy` (default: built-in release policy): optional policy YAML path in the consumer repository.
- `output-dir` (default: `artifacts/assurance-gate`): directory where gate artifacts are written.
- `environment` (default: empty): optional release-policy environment key such as `staging` or `production`.
- `fail-on-block` (default: `true`): fail the action when policy evaluation returns `block`.

## Minimal evidence bundle

A one-workflow-file consumer can start with `artifacts/evidence.json`:

```json
{
  "evidence": [
    {
      "claimId": "minimal-assurance-gate-reviewable",
      "lane": "spec",
      "kind": "schema",
      "sourceKind": "spec-derived",
      "origin": "consumer-fixture"
    }
  ],
  "policyEvidence": ["postDeployVerify", "qualityGates"]
}
```

The action writes:

- `assurance-summary.json`
- `policy-decision.json`
- `review-surface.md`
- `gate-result.json`
