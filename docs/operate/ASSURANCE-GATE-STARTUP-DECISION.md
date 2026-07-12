---
docRole: ssot
lastVerified: '2026-07-11'
owner: product-assurance
verificationCommand: pnpm -s exec vitest run tests/scripts/assurance-gate-startup-benchmark.test.ts tests/scripts/assurance-gate-cache-comparison.test.ts --reporter dot
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
OS/architecture, declared pnpm version, and the action ref's `pnpm-lock.yaml`
digest. The optimization
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

## Final comparison evidence

- Successful workflow run:
  `https://github.com/itdojp/ae-framework/actions/runs/29172844714`
- Exact ref: `7f2bed283cd5bd5550d91fec6e6d607d8d50f60a`
- Raw JSON:
  `artifacts/reference/benchmarks/assurance-gate-cache-comparison-2026-07-11.json`
- Raw Markdown:
  `artifacts/reference/benchmarks/assurance-gate-cache-comparison-2026-07-11.md`
- JSON SHA-256:
  `38f61562c78d193eaf1dbc420b86817e711c5c634dd6ea22ca42ceb137c33045`
- Markdown SHA-256:
  `06eff1af7cc6698b1c07368f7f0dc940e5012c46be80d348382619176021dc37`
- Environment: `ubuntu24-20260705.232.1`, Linux x64, Node `v20.20.2`,
  npm `10.8.2`, pnpm `10.0.0`.
- Fixture: `external-minimal-pass`; five cache-disabled samples and five exact
  cache-hit samples; all ten policy results were `pass`; every enabled sample
  restored the same exact key.

The tracked JSON and Markdown are byte-for-byte copies of the successful run's
uploaded comparison artifact. The workflow validated the JSON against
`schema/assurance-gate-cache-comparison.schema.json` before upload.

## Comparison result

| Mode | Minimum | Median | Maximum | p90 |
| --- | ---: | ---: | ---: | ---: |
| cache disabled / unique empty store | 10,968 ms | 11,876 ms | 12,443 ms | 12,443 ms |
| exact action-owned pnpm-store hit | 10,223 ms | 12,571 ms | 13,704 ms | 13,704 ms |

The exact-hit median was 695 ms slower, so the measured improvement ratio was
-5.85% (a 5.85% regression). Functional parity and 5/5 exact hits were proven,
but the 20% retention target was not met.

An earlier diagnostic run
[29172437742](https://github.com/itdojp/ae-framework/actions/runs/29172437742)
also remained below target (7.29%) but recorded pnpm as unavailable after
action-local Corepack cleanup. It is retained only as diagnostic history; the
final decision uses run 29172844714, which captured pnpm `10.0.0` inside the
composite action and passed the complete comparison contract.

## Final decision

`rollback-pnpm-store-cache`.

The cache adds restore/save/key/cleanup complexity without a repeatable measured
benefit under the selected external-style fixture. The final implementation
therefore removes the experimental action input, outputs, restore/save steps,
version instrumentation, and one-off comparison workflow from both action entry
points. Existing install/build/gate behavior and frozen-lockfile enforcement are
restored unchanged. The monthly/manual startup benchmark remains available for
remeasurement.

The current hosted cold median is well below 60 seconds and #3640 has not
recorded live-pilot startup friction, so a larger prebuilt/bundled architecture
is not justified now. Follow-up #3648 preserves explicit entry criteria,
provenance/compatibility requirements, and rollback expectations if later
adoption evidence crosses that boundary.

This decision is limited to action startup/runtime overhead. It does not claim
review-speed, productivity, quality, approval, or safety improvement.
