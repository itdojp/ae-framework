# Assurance Gate pnpm-store cache comparison

- Exact ref: `7f2bed283cd5bd5550d91fec6e6d607d8d50f60a`
- Workflow run: 29172844714
- Environment: ubuntu24-20260705.232.1, v20.20.2, pnpm 10.0.0
- Samples: cache miss=5, exact cache hit=5
- Functional parity: true
- Exact cache hits: 5/5

| Mode | Minimum (ms) | Median (ms) | Maximum (ms) | p90 (ms) |
| --- | ---: | ---: | ---: | ---: |
| cache disabled/miss | 10968.00 | 11876.00 | 12443.00 | 12443.00 |
| exact pnpm-store cache hit | 10223.00 | 12571.00 | 13704.00 | 13704.00 |

- Median improvement: -5.85%
- 20% target met: false
- Recommended outcome: `rollback-pnpm-store-cache`

> This comparison measures action startup/runtime overhead only. It is not evidence of review speed, productivity, code quality, approval, or safety improvement.
