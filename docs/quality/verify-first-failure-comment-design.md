# Verify-first Failure Diagnostic PR Comment Design

> `verify-first-failure-diagnostic-template.md` を PR 自動コメントに接続するための設計案

## 1. 目的

- Required / Opt-in gate 失敗時に、PR 上で最小診断情報を欠落なく提示する。
- 再実行・修正・fail-open の判断を PR 上で完結できる状態にする。

## 2. 入力（テンプレ項目との対応）

入力ソース:
- CI check context（workflow/job/status/url）
- `docs/quality/verify-first-failure-diagnostic-template.md`
- PR metadata（head SHA、labels、related issue）

テンプレ項目へのマッピング:
- Context: PR番号、SHA、失敗gate、検出時刻
- Symptom: 失敗job名、先頭失敗step、短いエラー要約
- Impact: gate の blocking level（Required/Opt-in）
- Reproduction: ローカル再現コマンド（gate別の既定値）
- Spec/Policy linkage: Specパス、AC参照、関連ポリシー
- Evidence: CI run URL、artifact path

## 3. コメント生成ルール（案）

1. 同一 head SHA + 同一 gate で既存 bot コメントがある場合は更新（upsert）する。  
2. Required gate 失敗時は fail-closed を明記し、merge 不可を宣言する。  
3. Opt-in gate 失敗時は fail-open 可否を明記し、follow-up issue の有無をチェックする。  
4. コメント末尾に「次アクション（再実行 / 修正 / fail-open）」を必ず出力する。  

## 4. PRコメント雛形（最小）

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

## 5. 実装ポイント（GitHub Actions）

- workflow: 既存の PR ゲート workflow の `failure()` パスでコメント処理を呼び出す。  
- 実装手段:
  - `actions/github-script` で upsert 実装
  - もしくは `gh pr comment` + 既存コメント検索で置換
- 追加メタ:
  - HTMLコメントマーカー（例: `<!-- verify-first-failure:<gate>:<sha> -->`）で同一コメントを識別

## 6. 段階導入

1. Phase-1: report-only（コメント投稿のみ、merge 制御は既存 gate に委譲）  
2. Phase-2: Required gate のみ自動診断コメントを必須化  
3. Phase-3: Opt-in gate まで展開し、follow-up issue チェックを自動化  

## 7. 非対象（この設計で扱わない範囲）

- 失敗原因の自動修復
- 複数workflow横断の根本原因推定
- 人手レビュー代替の自動承認
