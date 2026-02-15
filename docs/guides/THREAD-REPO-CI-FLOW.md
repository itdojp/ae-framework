# Thread -> Repo -> CI Flow Guide (Plan -> Spec Normalization)

> Language / 言語: English | 日本語

---

## English (Summary)

This guide standardizes how conversation plans are normalized into repository SSOT, then validated in CI with traceable evidence.

---

## 日本語

## 1. 目的

Plan（会話資産）を直接実装の正にせず、repo 上の Spec を SSOT として固定するための運用手順です。  
本ガイドは特定のIssueに依存しない一般的な運用標準です。

## 2. 入力/出力/更新タイミング

| フェーズ | 入力 | 出力 | 更新タイミング |
| --- | --- | --- | --- |
| Thread 整理 | 会話Plan、Issue、制約、リスク | Plan要約（作業メモ） | 作業開始時 |
| Repo 正規化 | Plan要約 | `docs/templates/plan-to-spec-normalization-template.md` を埋めたSpec草案 | PR作成前 |
| CI 検証 | Spec草案、ゲート定義 | ゲート合否、Evidence（summary/log） | PR更新ごと |
| Evidence 固定 | CI結果、再現手順 | PR本文/コメントのトレーサビリティ記録 | Review前/マージ前 |

## 3. 標準手順

### Step 0: Thread でPlanを整理
- 要件、スコープ、受入条件、非機能、制約を抽出する。
- ここでの成果物は作業メモ。SSOTではない。

### Step 1: Repo に正規化
- `docs/templates/plan-to-spec-normalization-template.md` をコピーして作業対象のSpecへ反映。
- 最低限、以下を埋める:
  - Goal/Scope
  - AC（Given/When/Then）
  - NFR
  - Verification Plan（Required/Optional gates）
  - Traceability Map

### Step 2: CI で機械判定
- Required gates（例: lint/test/review gate/verify-lite）を実行。
- 必要に応じて formal/security/adapters/qa を opt-in 実行。

### Step 3: Evidence を固定
- CI run URL、結果要約、再現コマンドをPRに記録。
- Plan item -> Spec artifact -> Gate -> Evidence の対応をPRで参照可能にする。

## 4. トレーサビリティ記載例（PR向け）

| Source plan/thread | Spec path | Gate | Evidence |
| --- | --- | --- | --- |
| Issue/Thread URL | `docs/templates/plan-to-spec-normalization-sample.md` | verify-lite | CI URL + `artifacts/verify-lite/verify-lite-run-summary.json` |

## 5. 失敗時の再実行手順

1. 失敗ゲートを特定（例: review gate / verify-lite）。  
2. 関連する Spec/AC/NFR の差分を確認。  
3. 必要なら Plan から再抽出し、正規化テンプレートの該当欄を更新。  
4. ローカル再現（可能な範囲）後に push。  
5. CI rerun 実施後、PRのEvidence欄を更新。

## 6. レビュー観点（最小）

- Planの要求が Spec に固定されているか
- AC/NFR と実装変更の対応が明確か
- Required gate の合否と再現導線があるか
- Out-of-scope が明示されているか

## 7. 関連ドキュメント

- `docs/templates/plan-to-spec-normalization-template.md`
- `docs/templates/plan-to-spec-normalization-sample.md`
- `docs/strategy/CODEX-AE-BOUNDARY-VERIFY-FIRST.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
