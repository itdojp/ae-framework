# Spec & Verification Kit Minimum Activation Example

This is a runnable fixture for the minimum TypeScript Spec & Verification Kit
activation profile. It demonstrates one requirement fragment linked to both BDD
and property examples through `@trace:REQ-SVK-001`.

## Run the example suites only

```bash
pnpm run spec-kit-min:verify -- \
  --profile-root examples/spec-verification-kit-min \
  --run-custom-suites \
  --skip lint \
  --skip types \
  --skip fast \
  --skip property-smoke
```

The command writes:

- `artifacts/spec-kit-min/activation-summary.json`
- `artifacts/spec-kit-min/activation-summary.md`

## Run the full repository activation profile

From an activated repository, run:

```bash
pnpm run spec-kit-min:verify -- --run-custom-suites
```

The baseline checks (`lint`, `types`, `test:fast`, and built-in
`test:property`) are separate from authored custom BDD/property suites. If
custom suites are discovered but `--run-custom-suites` is omitted, the summary
records a warning that explains the distinction.
