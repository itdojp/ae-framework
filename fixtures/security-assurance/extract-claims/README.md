# Security claim extraction fixture

This fixture exercises the deterministic `ae security extract-claims` MVP added for the Security Assurance Lane.

The extractor intentionally reads explicit `SEC-CLAIM:` blocks from Markdown instead of calling an external LLM. Each block is converted into `security-claim/v1`, schema-validated, and accompanied by a Markdown summary.

Example:

```bash
pnpm run security:extract-claims -- \
  --spec fixtures/security-assurance/extract-claims/spec.md \
  --out artifacts/security/security-claims.json \
  --generated-at 2026-05-07T00:00:00.000Z
```

Supported MVP fields include `id`, `type`, `criticality`, `targetLevel`, `statement`, `stride`, `cwe`, `sourceUri`, `sourceSection`, `boundaryIds`, `entryPoints`, `attackerControlled`, `dataClasses`, `requiredLanes`, and `notes`.
