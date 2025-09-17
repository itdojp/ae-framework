## Cedar Policies Quality Gates (report-only)

This workflow scans `policies/cedar/` for `.json` (Cedar JSON) and `.cedar` files and produces a non-blocking summary.

- Runner: `scripts/policies/validate-cedar.mjs`
- Artifact: `artifacts/policies/cedar-summary.json`
- PR Comment Header: `<!-- AE-CEDAR-SUMMARY -->`
- Trigger: add label `run-security` (or `run-cedar`)
- Enforcement: add label `enforce-security` (fails when NG > 0)

Environment (optional):
- `CEDAR_POLICIES_DIR`: directory to scan (default: `policies/cedar`)
- `CEDAR_SUMMARY`: output JSON path (default: `artifacts/policies/cedar-summary.json`)

JSON structure (minimal):
```
{
  "tool": "cedar-validator",
  "dir": "policies/cedar",
  "filesScanned": 3,
  "jsonFiles": 2,
  "cedarFiles": 1,
  "okCount": 3,
  "ngCount": 0,
  "errors": [ { "file": "...", "kind": "json-parse", "message": "..." } ],
  "results": [ { "file": "...", "type": "json|cedar", "valid": true|false } ],
  "timestamp": "..."
}
```

Notes:
- The validator performs minimal schema checks for JSON (presence of `policySet` or `policies` array-like structure). The text `.cedar` files are checked as non-empty.
- This is a report-only gate by default. Add `enforce-security` to make NG > 0 fail the job.

