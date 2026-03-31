---
docRole: derived
canonicalSource:
- SECURITY.md
- docs/ci/automation-permission-boundaries.md
- docs/ci/OPT-IN-CONTROLS.md
lastVerified: '2026-03-31'
---

# Agents Runbook: Security

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when security-oriented jobs fail, including scan, audit, and secrets lanes
- when dependency updates need a minimum security review before requesting merge

### What to load (primary sources)
- `SECURITY.md`
- `docs/ci/automation-permission-boundaries.md`
- `docs/ci/OPT-IN-CONTROLS.md`

### Commands (copy/paste)
```bash
pnpm -s run verify:security
```

```bash
pnpm -s run security:scan
```

```bash
pnpm -s run security:audit
```

```bash
pnpm -s run security:secrets
```

### Artifacts to check
- `artifacts/security/*`
- `artifacts/sbom/*`
- Step Summary from security-oriented workflows

### Escalation / follow-up
- even when you suspect a false positive, record the exclusion rationale in the PR or incident log
- for high-risk changes, record `run-security` label usage together with the latest `policy-gate` result
- when a secrets finding or a high-severity dependency issue is confirmed, stop merge progression and escalate through the repository security process in `SECURITY.md`

## 日本語

### When to use
- セキュリティ系ジョブ（scan / audit / secrets）の失敗対応を行うとき
- 依存更新時に、merge 依頼前の最低限の安全確認を行うとき

### What to load (primary sources)
- `SECURITY.md`
- `docs/ci/automation-permission-boundaries.md`
- `docs/ci/OPT-IN-CONTROLS.md`

### Commands (copy/paste)
```bash
pnpm -s run verify:security
```

```bash
pnpm -s run security:scan
```

```bash
pnpm -s run security:audit
```

```bash
pnpm -s run security:secrets
```

### Artifacts to check
- `artifacts/security/*`
- `artifacts/sbom/*`
- Security 系 workflow の Step Summary

### Escalation / follow-up
- 誤検知の可能性がある場合でも、除外根拠を PR または incident log に明記する
- 高リスク変更では、`run-security` ラベル運用と最新の `policy-gate` 判定結果をあわせて記録する
- secrets 検知や high severity の dependency issue が確定した場合は、merge を止めて `SECURITY.md` の repository security process に従って escalate する
