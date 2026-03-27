---
docRole: derived
canonicalSource:
- docs/quality/verify-first-implementation-runbook.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-03-27'
---
# Verify-first Failure Diagnostic Template

> Language / 言語: English | 日本語

---

## English

> Minimum diagnostic template for PR / CI failures, including reproducible local steps.

### 0. Context

- PR / Issue:
- Commit SHA:
- Failed gate:
- Detection time (UTC):

### 1. Symptom

- Error summary:
- First failing step:
- Scope (files/modules):

### 2. Impact

- Blocking level: Required / Opt-in
- User impact:
- Release impact:

### 3. Reproduction

- Local command(s):
  ```bash
  # Example: same entrypoint as Verify Lite / PR-blocking
  pnpm run verify:lite
  ```
- Expected:
- Actual:

### 4. Spec / Policy linkage

- Related spec path(s):
- Related acceptance criteria:
- Related policy / contract:

### 5. Root-cause hypothesis

- Hypothesis-1:
- Hypothesis-2:

### 6. Fix plan

- Immediate fix:
- Additional tests / checks:
- Rollback plan (if needed):

### 7. Evidence

- CI run URL:
- Artifact path(s):
- Log excerpt location:

### 8. Decision

- [ ] Re-run only
- [ ] Fix + re-run
- [ ] Fail-open (temporary) + follow-up issue
- Follow-up issue (required for fail-open):

## 日本語

> PR/CI 失敗時の最小診断テンプレート（再現手順付き）

### 0. Context / コンテキスト

- PR / Issue:
- Commit SHA:
- Failed gate:
- Detection time (UTC):

### 1. Symptom / 現象

- Error summary:
- First failing step:
- Scope (files/modules):

### 2. Impact / 影響

- Blocking level: Required / Opt-in
- User impact:
- Release impact:

### 3. Reproduction / 再現

- Local command(s):
  ```bash
  # 例: Verify Lite / PR-blocking と同じエントリポイント
  pnpm run verify:lite
  ```
- Expected:
- Actual:

### 4. Spec / Policy linkage / 仕様・ポリシーとのひも付け

- Related spec path(s):
- Related acceptance criteria:
- Related policy / contract:

### 5. Root-cause hypothesis / 原因仮説

- Hypothesis-1:
- Hypothesis-2:

### 6. Fix plan / 対処計画

- Immediate fix:
- Additional tests / checks:
- Rollback plan (if needed):

### 7. Evidence / 証跡

- CI run URL:
- Artifact path(s):
- Log excerpt location:

### 8. Decision / 決定

- [ ] Re-run only
- [ ] Fix + re-run
- [ ] Fail-open (temporary) + follow-up issue
- Follow-up issue (required for fail-open):
