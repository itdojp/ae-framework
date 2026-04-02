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

### 0. コンテキスト

- PR / Issue:
- Commit SHA:
- 失敗した gate:
- 検知時刻 (UTC):

### 1. 現象

- エラー要約:
- 最初の失敗ステップ:
- 影響範囲 (files/modules):

### 2. 影響

- Blocking level: Required / Opt-in
- ユーザー影響:
- リリース影響:

### 3. 再現

- ローカル再現コマンド:
  ```bash
  # 例: Verify Lite / PR-blocking と同じエントリポイント
  pnpm run verify:lite
  ```
- 期待結果:
- 実際の結果:

### 4. 仕様・ポリシーとのひも付け

- 関連 spec path:
- 関連 acceptance criteria:
- 関連 policy / contract:

### 5. 原因仮説

- 仮説-1:
- 仮説-2:

### 6. 対処計画

- 即時修正:
- 追加 tests / checks:
- Rollback plan (必要なら):

### 7. 証跡

- CI run URL:
- Artifact path:
- Log excerpt location:

### 8. 決定

- [ ] Re-run only
- [ ] Fix + re-run
- [ ] Fail-open (temporary) + follow-up issue
- Follow-up issue (fail-open 時は必須):
