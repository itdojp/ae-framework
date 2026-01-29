# Comparator Utilities

This document describes the shared comparator utility used for threshold parsing, comparisons, and strictest-merge decisions.

## Expression format

```
[operator][number][unit?]
```

- Operators: `>`, `>=`, `<`, `<=`, `==`, `!=`
- Default operator: `>=` (when omitted)
- Example expressions: `>=0.9`, `<=200ms`, `90%`, `==0`

## Supported units

### Percent

- `%`, `percent`, `pct`
- Normalization: stored as percent value (e.g., `90%` -> `90`)
- Actual values: when comparator is percent, `0.85` is treated as `85`

### Time

- `ms`, `s`, `m`, `h` (and common aliases like `sec`, `min`, `hour`)
- Normalization: converted to milliseconds (ms)

### Throughput

- `rps`, `req/s`, `requests/s`, `ops/s`
- `rpm`, `req/min`, `requests/min`, `ops/min`
- Normalization: converted to requests per second (rps)

### Unitless

- No unit specified
- Use for ratios or counts when units are implicit

## Strictest merge rules

When combining two threshold expressions:

- `>=` and `>`: the larger normalized value is stricter
- `<=` and `<`: the smaller normalized value is stricter
- Same value: strict operator (`>` or `<`) is stricter than non-strict (`>=` or `<=`)
- `==` can be used only if it satisfies the other comparator
- `!=` is not supported for strictest selection
- Unit mismatch is rejected

## Usage guidelines

- Prefer explicit units (`ms`, `%`, `rps`) to avoid ambiguity.
- For accuracy/coverage, choose either ratio (`>=0.9`) or percent (`>=90%`) and keep it consistent.
- For latency, prefer `ms`-based thresholds.
- For throughput, use `rps` or `rpm` explicitly.
- Use `strictest` when merging policy thresholds with AE-IR or configuration hints.
