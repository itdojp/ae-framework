---
docRole: ssot
canonicalSource:
- profiles/minimal.yaml
- profiles/standard.yaml
- profiles/full.yaml
- scripts/profiles/dogfood-ci-profiles.mjs
- scripts/ci/run-verify-lite-local.sh
- .github/workflows/deploy-time-profiles.yml
lastVerified: '2026-07-06'
owner: quality-maintainers
verificationCommand: pnpm -s run profiles:dogfood -- --profile all --no-write
---

# Deploy-time profile dogfood policy

This document records the Phase 3 dogfood boundary for deploy-time profiles.

## Profile to CI mapping

| Repository CI surface | Deploy-time profile | Decision semantics |
| --- | --- | --- |
| `verify:lite` / Verify Lite required check | `minimal` | Required deploy-time checks: `verify-lite`, `policy-gate`, `gate`. The local `verify:lite` runner runs the minimal profile replay during the existing Verify Lite pipeline after the root build and before state-machine/context-pack checks. |
| Current PR verification | `standard` | Same required checks as minimal, with Context Pack / property / MBT / conformance lanes recorded as advisory profile lanes where present. |
| Nightly and label-gated heavy lanes | `full` | Same required checks as current PR gating, with formal, mutation, and heavy-test trend lanes recorded as advisory profile lanes unless a future policy promotes them. |

## Replay evidence

Run:

```bash
pnpm -s run profiles:dogfood -- --profile all --fixture fixtures/profiles/dogfood/recent-pr-gate-decisions.json
```

The replay uses `@ae-framework/core` to validate `profiles/{minimal,standard,full}.yaml`, aggregate
profile evidence, and evaluate required-check decisions from the deterministic fixture. The fixture
contains 20 documented PR-equivalent cases and covers both pass and blocking outcomes.

## Required all-profile path check

The `Deploy-Time Profiles / deploy-time-profiles` check is intentionally emitted for every PR so it
can be named in branch protection without leaving non-profile PRs waiting for a skipped workflow.
Inside the job, `.github/workflows/deploy-time-profiles.yml` performs the path filter and runs the
all-profile replay only when a PR or `main` push touches one of these release-critical surfaces:

- `packages/core/**`
- `profiles/**`
- `schema/assurance-profile.schema.json`
- `fixtures/profiles/dogfood/**`
- `.github/actions/assurance-gate/**`
- root `action.yml`
- `scripts/actions/assurance-gate.mjs`
- `scripts/profiles/**`
- `.github/workflows/deploy-time-profiles.yml`
- `.github/branch-protection.main.verify-lite-trace-noreview.json`

For PR events, the workflow compares `merge-base(base, head)..head` so changes that landed only on
`main` after the PR branch was created do not make unrelated PRs run the expensive replay. When the
path filter matches, the job runs `pnpm -s run profiles:validate` and
`pnpm -s run profiles:dogfood -- --profile all`, then asserts that all three built-in profiles
(`minimal`, `standard`, `full`) executed and the replay status is `pass`.

## Drift handling

A drift is any case where the profile-derived required-check decision differs from the recorded
current CI decision. The dogfood report exits non-zero when drift is present. Drift must be fixed
in the profile mapping or documented in a follow-up issue before merge.

The report is intentionally a repository dogfood signal, not a new external adoption claim. It does
not publish Marketplace or npm assets; that remains Phase 4.
