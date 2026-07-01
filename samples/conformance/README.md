# Conformance Sample

Generate sample files and run verification:

- Generate: `pnpm run conformance:sample`
- Verify selected trace: `pnpm run conformance:verify:selected-trace`
- Verify generic sample/rules data: `pnpm run conformance:verify:sample`

Outputs
- Selected trace summary: `artifacts/hermetic-reports/conformance/selected-trace-summary.json`
- Generic sample results: `artifacts/hermetic-reports/conformance/sample-results.json`
- Sample files: `samples/conformance/`

Included sample trace
- `sample-traces.json` is checked in for default `verify:conformance`, `trace:validate`, and `conformance:verify:selected-trace` runs.
- Use `pnpm run conformance:sample` when you need a fresh rules/config/data set.
- For a different selected trace, validate that fixture with `pnpm run trace:validate -- --in <trace>` and append conformance overrides, for example `pnpm run conformance:verify:selected-trace -- --in <trace> --out <summary>`.
