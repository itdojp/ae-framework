# ajv Validation Failures: Examples & Messaging (#408)

Examples
- Missing required `adapter`:
```
error: data must have required property 'adapter' at artifacts/jest/summary.json
```
- Invalid `status`:
```
error: data.status must be equal to one of the allowed values (ok|warn|error)
```
- Property summary missing `seed`:
```
error: data must have required property 'seed' at artifacts/properties/summary.json
```

Messaging Policy
- Show file path and offending key; include `traceId` if present.
- Fail fast; aggregate multiple errors but keep output concise.
- Suggest fix links to schema paths under `docs/schemas/`.
