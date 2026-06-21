# Context Pack Boundary Map Validation Report

- GeneratedAt: 2026-06-21T00:00:00.000Z
- Status: REVIEW
- Map: `spec/context-pack/boundary-map.json`
- Schema: `schema/context-pack-boundary-map.schema.json`
- Context pack files: 1
- Skipped auxiliary files: 0
- Checked slices: 2
- Produced refs: 1
- Consumed refs: 1
- Findings: 2

## Summary
- duplicate slice ids: 0
- missing context-pack refs: 0
- duplicate produced refs: 0
- missing upstream slices: 0
- missing upstream producers: 0
- slice dependency cycles: 0

## Findings
- warning/issue-scope-outside-target: src/payments/settlement-retry.ts — The changed file is outside the intended sample Issue scope and needs reviewer disposition before merge.
- warning/boundary-map-slice-mismatch: spec/context-pack/boundary-map.json — The sample demonstrates how a changed-file list can drift away from the Context Pack slice being reviewed.
