# Quickstart — Comparator and Meta

This quickstart shows two tiny utilities to help reason about thresholds and report metadata.

Prerequisites
- Node.js 20+

Comparator Demo
1) Run the demo:
   - `node examples/comparator-demo.mjs`
2) Output shows A/B coverage thresholds and a strictest merge where higher is better for coverage metrics.

Report Meta Dump
1) Generate or place reports under `reports/` or `artifacts/`.
2) Run:
   - `node examples/report-meta-dump.mjs`
3) Output prints JSON lines with the file path, metadata keys, and a small sample.

Notes
- For enforcement, thresholds are governed by `policy/quality.json` (SSOT). See `docs/quality/precedence.md` for precedence and migration from `ae.config`.

