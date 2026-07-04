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

## 15-minute quickstart

Use `docs/getting-started/QUICKSTART-15MIN.md` for the one-workflow-file
external repository preview path. The quickstart shows both pass and block gate
decisions and writes the review surface to the GitHub Actions job summary.

Before the `v1` action tag and Marketplace listing are published, use `@main` or
an explicit commit SHA for preview validation. After the release tag exists, use
`itdojp/ae-framework/.github/actions/assurance-gate@v1`.

## Marketplace listing metadata draft

| Field | Value |
| --- | --- |
| Name | ae-framework Assurance Gate |
| Description | Validate assurance artifacts, evaluate a deploy-time profile policy, and render a PR review surface. |
| Branding | `shield` / `blue` |
| Primary category | Code quality |
| Secondary category | Security |
| Quickstart | `docs/getting-started/QUICKSTART-15MIN.md` |
| Compatibility | `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` |

Publication boundary: this repository contains Marketplace listing draft metadata
for the subdirectory action. Marketplace publication is not complete, and is not
ready, until the release owner adds a root `action.yml` shim or moves the action
to a dedicated action repository and publishes the listing.

## Version compatibility

The action builds `@ae-framework/core` from the same action repository ref that
supplies `profiles/`, `policy/`, and the curated schema bundle. Keep the action
ref, profiles, schemas, and core package release line aligned. See
`docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` for the compatibility
matrix and the `@main`/commit-SHA/`@v1` transition.
