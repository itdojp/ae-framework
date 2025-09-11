# Validating Artifacts with ajv-cli (#408)

Install
```bash
npm i -D ajv ajv-cli
```

Validate (examples)
```bash
# Adapter summary
npx ajv -s docs/schemas/artifacts-adapter-summary.schema.json -d artifacts/*/summary.json --strict=false

# Formal summary
npx ajv -s docs/schemas/formal-summary.schema.json -d formal/summary.json --strict=false

# Property summary (single or each element when array)
# If array, use: jq -c '.[]' artifacts/properties/summary.json | while read -r item; do echo "$item" | npx ajv -s docs/schemas/artifacts-properties-summary.schema.json -d /dev/stdin --strict=false; done
```

CI Notes
- Fail the job on validation errors; attach offending file paths.
- Keep `--strict=false` for forward-compat; schemas may evolve.
