---
docRole: derived
canonicalSource:
- docs/quality/verify-first-implementation-runbook.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-04-06'
---
# Verify-first Failure Diagnostic Template

> Language / 言語: English | 日本語

---

## English

> Minimum diagnostic template for PR / CI failures, including reproducible local steps.

### 0. Context

- PR / issue:
- commit SHA:
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

- CI 実行 URL:
- Artifact path(s):
- ログ抜粋箇所:

### 8. Decision

- [ ] 再実行のみ
- [ ] 修正して再実行
- [ ] Fail-open (temporary) + follow-up issue
- Follow-up issue (required for fail-open):

## 日本語

> PR/CI 失敗時の最小診断テンプレート（再現手順付き）

### 0. コンテキスト

- PR / issue:
- commit SHA:
- 失敗したゲート:
- 検知時刻 (UTC):

### 1. 現象

- エラー要約:
- 最初の失敗ステップ:
- 影響範囲（ファイル / モジュール）:

### 2. 影響

- ブロッキング区分: 必須 / オプトイン
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

- 関連する spec path（複数可）:
- 関連する acceptance criteria:
- 関連する policy / contract:

### 5. 原因仮説

- 仮説-1:
- 仮説-2:

### 6. 対処計画

- 即時修正:
- 追加の tests / checks:
- ロールバック計画 (必要なら):

### 7. 証跡

- CI 実行 URL:
- 成果物パス（複数可）:
- ログ抜粋箇所:

### 8. 決定

- [ ] 再実行のみ
- [ ] 修正して再実行
- [ ] Fail-open（temporary）+ follow-up issue を起票
- Follow-up issue（fail-open 時は必須）:
