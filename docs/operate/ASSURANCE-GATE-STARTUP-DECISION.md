---
docRole: ssot
lastVerified: '2026-07-11'
owner: product-assurance
verificationCommand: node scripts/actions/validate-assurance-gate-startup-benchmark.mjs artifacts/reference/benchmarks/assurance-gate-startup-2026-07-11.json
---

# Assurance Gate startup optimization decision

This record evaluates the Issue #3641 optimization rule from a reviewed,
GitHub-hosted-runner baseline. It concerns action startup/runtime overhead only.
It is not evidence of review speed, productivity, quality, approval, or safety
improvement.

## Baseline evidence

- Successful workflow run:
  `https://github.com/itdojp/ae-framework/actions/runs/29170591202`
- Exact ref: `e53b8a1761c733d9f6a60080297889a805bc8c63`
- Raw JSON:
  `artifacts/reference/benchmarks/assurance-gate-startup-2026-07-11.json`
- Raw Markdown:
  `artifacts/reference/benchmarks/assurance-gate-startup-2026-07-11.md`
- JSON SHA-256:
  `d04247546651a292bc99b29dc91420bfd5e0ee876edacb9e3d1fd3f89b8ac57b`
- Markdown SHA-256:
  `457704e26212a8bf881dff28f8ed459572aef54168b29d12bea71eca71fca5d5`
- Environment: `ubuntu24-20260705.232.1`, Linux x64, Node `v20.20.2`,
  npm `10.8.2`, pnpm `10.0.0` (measured).
- Fixture: `external-minimal-pass`; five cold and five warm samples; all ten
  policy results were `pass`; no collection errors.

The tracked JSON is a byte-for-byte copy of the uploaded workflow artifact. The
tracked Markdown differs only by removal of the generator's extra final blank
line so repository whitespace checks pass. The workflow's validator passed
before upload, and the command in this document's front matter validates the
tracked JSON independently.

## Observed medians

| Cache state | Total | Corepack/pnpm setup | Dependency install | Core build | Gate execution | Review rendering |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| cold | 10,837.08 ms | 1,352.29 ms | 7,721.49 ms | 1,533.08 ms | 191.55 ms | 0.094 ms |
| warm | 3,383.95 ms | 418.71 ms | 1,304.30 ms | 1,502.90 ms | 189.06 ms | 0.096 ms |

Workflow checkout/initialization was 1,543 ms and is recorded once outside the
per-sample totals. Review rendering is nested in gate execution and is not
double-counted.

## Rule evaluation

| Trigger | Threshold | Observed | Result |
| --- | --- | ---: | --- |
| Cold median total | `> 60,000 ms` | 10,837.08 ms | not triggered |
| Setup + install + build share | `> 70%` | 97.88% | **triggered** |
| Live-pilot startup friction | observed | not observed | not triggered |

The setup/install/build-share trigger requires one bounded optimization
evaluation. The gate itself is not the dominant phase; dependency installation
is the largest cold component.

## Selected bounded optimization

Evaluate an action-owned pnpm content-addressable-store cache keyed by runner
OS/architecture and the action ref's `pnpm-lock.yaml` digest. The optimization
must not cache consumer artifacts, `node_modules`, core build output, policy
results, or review surfaces. It must preserve the current action-ref alignment,
frozen lockfile enforcement, pass/block semantics, and both composite-action
entry points.

The implementation/comparison PR must:

1. use a cache key derived from the immutable lockfile content rather than a
   moving branch name;
2. avoid restore-key prefixes and record whether the exact cache hit occurred;
3. measure cache restore overhead separately rather than treating it as zero;
4. compare at least five cache-miss and five exact-cache-hit samples on the same
   GitHub-hosted runner class, Node/pnpm versions, fixture, and action ref class;
5. target at least 20% lower cache-hit total median than the 10,837.08 ms cold
   baseline while preserving all functional results;
6. retain the cache only if measured benefit and operational risk justify it;
   otherwise revert it and create a prebuilt/bundled release-surface follow-up.

## Current decision

`evaluate-one-low-risk-optimization`.

This is a selected implementation decision, not a completed performance claim.
Issue #3641 remains open until the cache experiment has a reviewed before/after
artifact and the final keep/rollback/follow-up outcome is recorded.
