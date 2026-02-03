# Conformance Sample

Generate sample files and run verification:

- Generate: `pnpm run conformance:sample`
- Verify: `pnpm run conformance:verify:sample`

Outputs
- Results: `artifacts/hermetic-reports/conformance/sample-results.json`
- Sample files: `samples/conformance/`

Included sample trace
- `sample-traces.json` is checked in for default `verify:conformance` / `trace:validate` runs.
- Use `pnpm run conformance:sample` when you need a fresh rules/config/data set.
