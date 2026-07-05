---
docRole: ssot
lastVerified: '2026-07-06'
owner: product-assurance
verificationCommand: pnpm -s exec vitest run tests/unit/docs/publish-assets-quickstart.test.ts --reporter dot
---

# Deploy-time profile compatibility

This page is the compatibility reference for the deploy-time adoption surface
introduced by Issue #3598: the `@ae-framework/core` package, the composite
`assurance-gate` action, the `profiles/*.yaml` contracts, and the curated schema
bundle used by the action.

## Current compatibility set

| Surface | Current repository value | Compatibility rule |
| --- | --- | --- |
| Core package | `@ae-framework/core` `0.1.0` | `0.1.x` is the initial pre-publication compatibility line for the curated schema bundle and pure-JS policy evaluator. |
| Action | root `action.yml` plus compatibility surface `.github/actions/assurance-gate/action.yml` | Pin the action to the same repository ref that supplies `profiles/`, `policy/`, and `packages/core`. Use `v1` for normal adoption after the release tag exists; use `v1.0.1` or a commit SHA for reproducibility. |
| Built-in profiles | `profiles/minimal.yaml`, `profiles/standard.yaml`, `profiles/full.yaml` | Profiles use `schemaVersion: assurance-profile/v1` and are validated before policy evaluation. |
| Release policy | `policy/release-policy.yml` | Built-in profiles default to `schemaVersion: ae-release-policy/v1`; custom policies must validate against the same schema. |
| Curated schema bundle | `packages/core/schema/*.json` | The package ships the schema copies that the standalone core validates; action, profiles, and schemas should be released from the same repository ref. |
| Node runtime | `>=20.11 <23` | Shared by the root repository and `@ae-framework/core` package metadata. |

## Version-skew boundary

The composite action builds `@ae-framework/core` from the action repository ref
that GitHub downloads for `uses: itdojp/ae-framework/.github/actions/assurance-gate@...`.
That means a consumer repository does not need a pnpm workspace or a separate
core package install for the one-workflow-file path. It also means the action
ref is the compatibility anchor: action metadata, built-in profiles, policy,
curated schemas, and core implementation should come from the same ref.

For external adoption after the root action release, prefer one of these forms:

```yaml
uses: itdojp/ae-framework@v1
# or, for a reproducible evaluation, use @v1.0.1 or pin a specific commit SHA from this repo.
```

The npm package is prepared as `@ae-framework/core@0.1.0`, but external
quickstart users should not assume that package is published until the release
notes explicitly say it is available on npm.

## Profile compatibility expectations

| Profile | README adoption level | Expected consumer change | Additional toolchain |
| --- | --- | --- | --- |
| `minimal` | Baseline | Change only the `profile` input or the `.ae/assurance.yml` profile value. | None beyond GitHub-hosted Node/Corepack inside the action. |
| `standard` | Structured assurance | Change `profile: minimal` to `profile: standard` and supply the additional evidence artifacts the profile declares. | Existing repository verification lanes may produce the richer evidence. |
| `full` | High-assurance critical core | Change `profile: standard` to `profile: full` when heavy/formal evidence is intentionally in scope. | Formal and heavy-test producers remain opt-in and repository-specific. |
| custom YAML path | Team-specific profile | Set `profile` to a path inside the consumer repository. | The file must validate as `assurance-profile/v1`; policy paths must stay inside the consumer workspace. |

Switching between built-in profiles is designed to be a one-line profile input
change. The resulting gate decision still depends on whether the selected
profile's required evidence is present.

## Supported schema versions in `@ae-framework/core@0.1.0`

The initial core package validates the curated minimal adoption set:

- `ae-handoff/v1`
- `artifact-metadata` envelope schema
- `assurance-profile/v1`
- `assurance-summary/v1`
- `change-package/v2`
- `claim-evidence-manifest/v1`
- `envelope` wrapper schema
- `policy-decision-v1` with schema version `1.0.0`
- `policy-gate-summary/v1`
- `producer-normalization-summary/v1`
- `ae-release-policy/v1`
- `verify-lite-run-summary` schema

The `standard` and `full` profiles may reference repository-root schemas that
are not in the minimal package bundle. Those profiles are available for this
repository's dogfood path and should be released with the same action ref when
external support is promoted beyond `minimal`.

## Replay evidence boundary

Deploy-time profile compatibility claims are backed by two repository-local replay modes:

| Mode | Backing fixture | What it supports | What it does not support |
| --- | --- | --- | --- |
| `documented-fixture-equivalent` | `fixtures/profiles/dogfood/recent-pr-gate-decisions.json` | Fast CI dogfood coverage for pass and blocking required-check outcomes. | A claim that the cases are raw captures from merged PRs. |
| `recorded-pr` | `fixtures/profiles/dogfood/recorded-pr-gate-decisions.json` | Decision-parity replay against 20 real merged PR check-rollups from this repository. | External repository adoption outcomes or blocking-case coverage; merged PRs are expected to be pass-only. |

The `Deploy-Time Profiles Recorded Replay` workflow runs the recorded fixture on a schedule and via
manual dispatch. Keep the fast fixture-equivalent replay as the PR path so branch-protection checks
remain bounded.

## Evidence links

- `tests/actions/assurance-gate-action.test.ts` exercises the action runner
  against a bare non-workspace fixture and records both pass and block behavior.
- `tests/cli/init-cli.test.ts` verifies `ae init --profile` workflow scaffolding.
- `tests/scripts/profile-dogfood.test.ts` verifies both the fast fixture-equivalent replay and the recorded-PR replay mapping used by deploy-time profile dogfooding.
- `docs/quality/DEPLOY-TIME-PROFILE-DOGFOOD.md` records the internal profile
  dogfood boundary, including the scheduled recorded-PR replay path.
