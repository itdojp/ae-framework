---
docRole: derived
canonicalSource:
- docs/quality/verify-first-implementation-runbook.md
- docs/ci/pr-automation.md
lastVerified: '2026-04-03'
---
# Verify-first Failure Diagnostic PR Comment Design

> Language / 言語: English | 日本語

---

## English

Design note for wiring `verify-first-failure-diagnostic-template.md` into automated PR comments.

### 1. Purpose

- Surface the minimum diagnostic information on the PR whenever a Required or Opt-in gate fails.
- Make re-run, fix, and fail-open decisions possible from the PR discussion alone.

### 2. Inputs and template mapping

Input sources:
- CI check context (`workflow`, `job`, `status`, `url`)
- `docs/quality/verify-first-failure-diagnostic-template.md`
- PR metadata (`head SHA`, labels, related issue)

Mapping to template fields:
- `Context`: PR number, SHA, failing gate, detection time
- `Symptom`: failing job name, first failing step, short error summary
- `Impact`: blocking level of the gate (`Required` or `Opt-in`)
- `Reproduction`: default local reproduce command for the gate
- `Spec/Policy linkage`: spec path, acceptance criteria reference, related policy
- `Evidence`: CI run URL, artifact path

### 3. Comment generation rules

1. Upsert when a bot comment already exists for the same `head SHA` and gate.
2. For Required gate failures, state fail-closed behavior and that merge is blocked.
3. For Opt-in gate failures, state whether fail-open is allowed and whether a follow-up issue exists.
4. Always end with explicit next actions: re-run, fix, or fail-open.

### 4. Minimal PR comment template

````md
### Verify-first Failure Diagnostic

- Gate: <workflow/job>
- Blocking: <Required|Opt-in>
- SHA: <head-sha>
- CI Run: <url>

#### Symptom
- <error summary>

#### Reproduction
```bash
<local reproduce command>
```

#### Spec/Policy linkage
- Spec: <path>
- AC: <id or text>
- Policy: <path>

#### Decision candidates
- [ ] Re-run only
- [ ] Fix + re-run
- [ ] Fail-open + follow-up issue
````

### 5. GitHub Actions implementation points

- Trigger the comment handler from the `failure()` path of the existing PR gate workflows.
- Implementation options:
  - use `actions/github-script` for upsert
  - or use `gh pr comment` plus marker-based comment replacement
- Additional metadata:
  - use an HTML marker such as `<!-- verify-first-failure:<gate>:<sha> -->` to identify the comment instance

### 6. Phased rollout

1. Phase 1: report-only comment posting, with merge control delegated to existing gates
2. Phase 2: require automated diagnostic comments for Required gates
3. Phase 3: extend to Opt-in gates and automate follow-up issue checks

### 7. Out of scope

- Automatic remediation of the failure
- Cross-workflow root-cause inference
- Automatic approval in place of human review

## 日本語

`verify-first-failure-diagnostic-template.md` を PR 自動コメントに接続するための設計案です。

### 1. 目的

- 必須 / オプトインゲート失敗時に、PR 上で最小診断情報を欠落なく提示する。
- 再実行・修正・fail-open の判断を PR 上で完結できる状態にする。

### 2. 入力（テンプレ項目との対応）

入力ソース:
- CI チェック文脈（`workflow`, `job`, `status`, `url`）
- `docs/quality/verify-first-failure-diagnostic-template.md`
- PR メタデータ（`head SHA`、labels、related issue）

テンプレ項目へのマッピング:
- `Context`: PR 番号、SHA、失敗ゲート、検出時刻
- `Symptom`: 失敗 job 名、先頭失敗 step、短いエラー要約
- `Impact`: ゲートのブロッキング区分（`Required` / `Opt-in`）
- `Reproduction`: ゲート別の既定ローカル再現コマンド
- `Spec/Policy linkage`: spec パス、AC 参照、関連ポリシー
- `Evidence`: CI run URL、成果物 path

### 3. コメント生成ルール

1. 同一 `head SHA` と同一 gate に対する既存 bot コメントがある場合は upsert する。
2. 必須ゲート失敗時は fail-closed を明記し、merge 不可を宣言する。
3. オプトインゲート失敗時は fail-open 可否と follow-up issue の有無を明記する。
4. コメント末尾に次アクション（再実行 / 修正 / fail-open）を必ず出力する。

### 4. PR コメント雛形（最小）

````md
### Verify-first Failure Diagnostic

- Gate: <workflow/job>
- Blocking: <Required|Opt-in>
- SHA: <head-sha>
- CI Run: <url>

#### Symptom
- <error summary>

#### Reproduction
```bash
<local reproduce command>
```

#### Spec/Policy linkage
- Spec: <path>
- AC: <id or text>
- Policy: <path>

#### Decision candidates
- [ ] Re-run only
- [ ] Fix + re-run
- [ ] Fail-open + follow-up issue
````

### 5. GitHub Actions 実装ポイント

- 既存の PR ゲート workflow の `failure()` パスでコメント処理を呼び出す。
- 実装手段:
  - `actions/github-script` で upsert を実装する
  - もしくは `gh pr comment` と marker ベースの置換を使う
- 追加メタ:
  - `<!-- verify-first-failure:<gate>:<sha> -->` のような HTML marker で同一コメントを識別する

### 6. 段階導入

1. Phase 1: report-only でコメント投稿のみ行い、merge 制御は既存ゲートに委譲する
2. Phase 2: 必須ゲートの自動診断コメントを必須化する
3. Phase 3: オプトインゲートまで展開し、follow-up issue チェックを自動化する

### 7. 非対象

- 失敗原因の自動修復
- 複数 workflow 横断の根本原因推定
- 人手レビューの代替となる自動承認
