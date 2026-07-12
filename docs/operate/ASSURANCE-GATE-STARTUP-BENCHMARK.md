---
docRole: ssot
lastVerified: '2026-07-11'
owner: product-assurance
verificationCommand: pnpm -s exec vitest run tests/scripts/assurance-gate-startup-benchmark.test.ts tests/scripts/assurance-gate-cache-comparison.test.ts tests/actions/assurance-gate-action.test.ts --reporter dot
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

The install command explicitly sets both `use-lockfile=true` and
`package-lock=true`. In this repository's pnpm 10 configuration,
`.npmrc` also contains `package-lock=false`; without the command-level override,
pnpm disables its lockfile and rejects `--frozen-lockfile`. The option name is
inherited npm configuration terminology: pnpm remains the installer and the
workflow verifies that no `package-lock.json` is created.

The harness uses the same setup/install/build/gate commands as the composite
action and an external-style non-workspace minimal-profile fixture. It records
at least five measured samples for each cache state:

- `cold`: remove linked `node_modules` and core build output, then use unique
  empty pnpm store and Corepack cache directories before every measured sample;
- `warm`: precondition one pnpm store and Corepack cache, linked dependencies, and core build, then
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
If pnpm setup fails before its version can be measured, the diagnostic report
uses the root `packageManager` version and marks `pnpmVersionSource` as
`configured-fallback`; a successful baseline requires `measured`.
Workflow checkout/init is recorded once as method metadata and is outside each
per-sample total; `actionInitialization` measures consumer-fixture preparation
inside each sample.
If a measured phase fails, the harness preserves an `error` sample with its
`errorPhase`, writes both reports, and exits non-zero so report-only evidence
does not conceal functional failure.
If warm-state preconditioning itself fails, the report records a
`collectionErrors` entry and an explicit missing-sample count instead of
fabricating warm timings. The workflow still uploads the diagnostic report and
fails; such a run is not a usable baseline.

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
After collecting the in-memory report, it removes the scratch consumer, pnpm
store, and Corepack cache before writing the selected JSON/Markdown outputs so
later repository lint and verification do not scan downloaded package-manager
implementation files.

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

## Current hosted baseline

The first successful GitHub-hosted baseline is preserved at:

- `artifacts/reference/benchmarks/assurance-gate-startup-2026-07-11.json`;
- `artifacts/reference/benchmarks/assurance-gate-startup-2026-07-11.md`.

Workflow run `29170591202` measured five cold and five warm passing samples on
exact ref `e53b8a1761c733d9f6a60080297889a805bc8c63`. The cold total median was
10,837.08 ms and setup + install + build represented 97.88%, so the 70% trigger
applied. `docs/operate/ASSURANCE-GATE-STARTUP-DECISION.md` records the bounded
optimization comparison and final rollback decision.

## Completed pnpm-store cache experiment

The bounded experiment measured five cache-disabled and five exact-cache-hit
action invocations on the same GitHub-hosted runner/tool class. The reviewed
reference reports are preserved at:

- `artifacts/reference/benchmarks/assurance-gate-cache-comparison-2026-07-11.json`;
- `artifacts/reference/benchmarks/assurance-gate-cache-comparison-2026-07-11.md`.

Run [29172844714](https://github.com/itdojp/ae-framework/actions/runs/29172844714)
used exact ref `7f2bed283cd5bd5550d91fec6e6d607d8d50f60a`, runner image
`ubuntu24-20260705.232.1`, Node `v20.20.2`, npm `10.8.2`, and pnpm `10.0.0`.
All ten functional results passed and all five enabled samples restored the same
exact cache key. Cache-disabled median total was 11,876 ms; exact-hit median
total was 12,571 ms, a -5.85% improvement (5.85% regression).

The experiment therefore missed the 20% retention target and was rolled back.
The public action inputs/outputs and runtime no longer include the experimental
dependency cache, and the one-off comparison workflow was removed. The
report-only cold/warm startup workflow remains the supported remeasurement
lane. This outcome does not establish a general performance or productivity
claim.

## External pilot recording

Operators for #3640 should record the same startup fields when friction occurs:
exact action ref, runner, cache state, setup/install/build/gate phase, elapsed
time, result, retry/manual intervention, and limitation. Missing timing remains
`not_collected`; it is not converted to zero.
