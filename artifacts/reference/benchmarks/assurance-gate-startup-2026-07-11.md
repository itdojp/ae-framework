# Assurance Gate startup benchmark

- Exact ref: `e53b8a1761c733d9f6a60080297889a805bc8c63`
- Fixture: `external-minimal-pass` (pass)
- Runner: linux/x64 (ubuntu24-20260705.232.1)
- Node/npm/pnpm: v20.20.2 / 10.8.2 / 10.0.0 (measured)
- Samples: cold=5, warm=5
- Cold results: pass=5, block=0, error=0
- Warm results: pass=5, block=0, error=0
- Workflow checkout/initialization: 1543.00 ms (recorded once, outside per-sample total)

| Cache | Phase | Minimum (ms) | Median (ms) | Maximum (ms) | p90 (ms) |
| --- | --- | ---: | ---: | ---: | ---: |
| cold | actionInitialization | 0.14 | 0.15 | 0.37 | 0.37 |
| cold | corepackPnpmSetup | 1278.46 | 1352.29 | 1359.21 | 1359.21 |
| cold | dependencyInstall | 7188.57 | 7721.49 | 8774.28 | 8774.28 |
| cold | coreBuild | 1473.30 | 1533.08 | 1584.37 | 1584.37 |
| cold | gateExecution | 189.92 | 191.55 | 209.80 | 209.80 |
| cold | reviewSurfaceRendering | 0.07 | 0.09 | 0.10 | 0.10 |
| cold | total | 10213.22 | 10837.08 | 11736.22 | 11736.22 |
| warm | actionInitialization | 0.20 | 0.23 | 0.29 | 0.29 |
| warm | corepackPnpmSetup | 417.12 | 418.71 | 428.27 | 428.27 |
| warm | dependencyInstall | 1129.54 | 1304.30 | 1905.63 | 1905.63 |
| warm | coreBuild | 1479.40 | 1502.90 | 1567.45 | 1567.45 |
| warm | gateExecution | 181.54 | 189.06 | 196.06 | 196.06 |
| warm | reviewSurfaceRendering | 0.07 | 0.10 | 0.10 | 0.10 |
| warm | total | 3307.31 | 3383.95 | 3998.42 | 3998.42 |

## Optimization assessment

- Cold median total > 60s: false
- Setup + install + build > 70%: true
- Setup/install/build share: 97.88%
- Live pilot friction observed: false
- Recommended outcome: `evaluate-one-low-risk-optimization`
- Final decision: `pending-reviewed-baseline`

> This report measures startup/runtime overhead only. It is not evidence of review speed, productivity, code quality, approval, or safety improvement.
