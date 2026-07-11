---
docRole: ssot
lastVerified: '2026-07-11'
owner: product-assurance
verificationCommand: pnpm -s exec vitest run tests/scripts/assurance-gate-startup-benchmark.test.ts tests/actions/assurance-gate-action.test.ts --reporter dot
---

# Assurance Gate startup benchmark

This runbook defines the report-only startup/runtime benchmark for the root
Assurance Gate action. It measures action overhead only; it is not evidence of
review speed, time-to-merge, productivity, quality, approval, or safety impact.

## Execution surface

- Workflow: `.github/workflows/assurance-gate-startup-benchmark.yml`
- Command: `pnpm -s run benchmark:assurance-gate-startup`
- JSON contract: `schema/assurance-gate-startup-benchmark.schema.json`
- Generated reports:
  - `artifacts/benchmarks/assurance-gate-startup.json`
  - `artifacts/benchmarks/assurance-gate-startup.md`

The workflow is manual and monthly scheduled. It is not triggered by
`pull_request`, is not a required check, and applies no wall-clock blocking
threshold to normal changes.

## Measurement method

The fixture inventory reuses the minimal pass/block evidence shape exercised by
`tests/actions/assurance-gate-action.test.ts`. The benchmark creates that shape
in a directory that is not a pnpm workspace package, then invokes the same
Corepack, filtered install, core build, and gate commands as both composite
action entry points. Existing action tests remain the authority for root and
compatibility-subdirectory output/pass/block parity.

The harness uses the same setup/install/build/gate commands as the composite
action and an external-style non-workspace minimal-profile fixture. It records
at least five measured samples for each cache state:

- `cold`: remove linked `node_modules` and core build output, then use a unique
  empty pnpm store before every measured sample;
- `warm`: precondition one pnpm store, linked dependencies, and core build, then
  invoke the unchanged setup/install/build/gate path for every measured sample.

Each sample records:

- consumer/action initialization;
- Corepack and pnpm setup;
- dependency install;
- core build;
- full gate process execution;
- review-surface rendering as an internal subphase of gate execution;
- total measured time and pass/block result.

The report also records the exact commit SHA, workflow checkout/init duration,
architecture and image, CPU/memory, Node/npm/pnpm versions, fixture ID, sample
count, the `pilotFriction` input, and minimum/median/maximum/p90 statistics. Review-surface rendering is
nested in `gateExecution`; it is not added a second time to `total`.
Workflow checkout/init is recorded once as method metadata and is outside each
per-sample total; `actionInitialization` measures consumer-fixture preparation
inside each sample.
If a measured phase fails, the harness preserves an `error` sample with its
`errorPhase`, writes both reports, and exits non-zero so report-only evidence
does not conceal functional failure.

## Run and validate

Run the GitHub workflow for the GitHub-hosted-runner baseline. A local run is
useful for harness diagnostics but must retain `runnerImage=local-unpinned` and
must not be substituted for the hosted baseline.

```bash
pnpm -s run benchmark:assurance-gate-startup -- --runs=5 --fixture=pass
pnpm -s run benchmark:assurance-gate-startup:validate
```

The harness intentionally removes and recreates installation state in its
checkout. Run it only in a dedicated worktree or ephemeral CI checkout, not in
a shared development workspace with uncommitted dependency state.

## Optimization decision rule

The machine report evaluates the Issue #3641 triggers:

1. cold median total exceeds 60 seconds;
2. cold median Corepack/setup + install + build exceeds 70% of cold median total;
3. live pilot #3640 records startup/runtime friction.

The first harness report leaves `finalDecision=pending-reviewed-baseline`.
After a successful run on `main`, preserve its JSON/Markdown artifact in a
reviewed baseline PR and choose one outcome:

- maintain the current runtime when no trigger applies;
- evaluate exactly one low-risk optimization when a trigger applies;
- create a separate architecture Issue when prebuilt/bundled release surfaces
  are required.

Any before/after comparison must use the same ref class, runner, versions,
fixture, cache definitions, and run count. Functional pass/block behavior takes
priority over elapsed time.

## External pilot recording

Operators for #3640 should record the same startup fields when friction occurs:
exact action ref, runner, cache state, setup/install/build/gate phase, elapsed
time, result, retry/manual intervention, and limitation. Missing timing remains
`not_collected`; it is not converted to zero.
