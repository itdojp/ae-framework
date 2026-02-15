# Verify-first 成果物カタログ（SSOT / AC / NFR / Evidence）

> Language / 言語: English | 日本語

---

## English (Summary)

Defines the minimum repository artifacts for Verify-first operations and clarifies ownership/review/storage responsibilities.

---

## 日本語

## 1. 目的

本ドキュメントは、`Conversation is not SSOT` を運用で担保するために、  
repo 上で管理すべき最小成果物（Spec / AC / NFR / 制約 / Evidence）を定義します。

対象: #1969 子Issue #1970

## 2. 最小成果物カタログ（必須 / 任意）

| 区分 | 必須 | 最小内容 | 保管場所（例） | 判定タイミング |
| --- | --- | --- | --- | --- |
| Spec（仕様本体） | 必須 | スコープ、要件、前提、変更履歴 | `spec/**/*.md`, `spec/**/*.yaml`, `spec/**/*.yml` | PRレビュー時 |
| AC（受入基準） | 必須 | Given/When/Then もしくは同等の合否条件 | Spec 内の AC セクション | PRレビュー時 |
| NFR（非機能） | 必須 | 性能/信頼性/セキュリティ/運用制約 | `spec/nonfunctional/*`, Spec 内 NFR | PRレビュー時 |
| 制約・前提 | 必須 | 技術制約、依存、除外スコープ | Spec 内 constraints / assumptions | PRレビュー時 |
| Gate 定義 | 必須 | Required/Optional ゲートの適用方針 | `spec/gates.yaml`, workflow 設定 | CI実行時 |
| Evidence（証跡） | 必須 | CI結果要約、再現コマンド、主要ログ導線 | `artifacts/**`, PR本文/コメント | CI完了時 |
| 形式手法レポート | 任意 | TLA+/Alloy/CSP/Lean などの結果 | `artifacts/hermetic-reports/formal/**` | opt-in 実行時 |
| 追加品質レポート | 任意 | Security / adapters / QA の結果 | `artifacts/**` | opt-in 実行時 |

## 3. 責務マトリクス（Owner / Reviewer / Storage）

| 成果物 | Owner（作成責任） | Reviewer（確認責任） | Storage（正） |
| --- | --- | --- | --- |
| Spec / AC / NFR / 制約 | 変更実装者（PR author） | レビュアー + CODEOWNERS | repository (`spec/**`) |
| Gate 定義 | CI/品質運用担当 + PR author | CI/品質レビュー担当 | repository (`.github/workflows/**`, `spec/gates.yaml`) |
| Evidence 要約 | CI（自動生成） + PR author（補足） | レビュアー | artifacts + PR thread |

## 4. 既存ドキュメントとの対応表

| 本カタログ項目 | 参照先（既存SSOT/契約） |
| --- | --- |
| Spec 配置規約 | `docs/spec/registry.md` |
| Artifacts の Required/Optional 契約 | `docs/quality/ARTIFACTS-CONTRACT.md` |
| フォーマル検証ゲート方針 | `docs/quality/formal-gates.md` |
| PR必須チェック運用 | `docs/ci-policy.md` |
| 品質運用フロー | `docs/quality/formal-runbook.md` |

## 5. PR運用チェック（最小）

- [ ] Spec/AC/NFR/制約の差分が repo 上でレビュー可能
- [ ] Required ゲートの合否が確認可能
- [ ] Evidence（CI要約と再現導線）が PR から辿れる
- [ ] Out-of-scope / Non-goals が明記されている

## 6. 備考

- Plan（会話資産）は入力であり、正は常に repo 成果物に固定する。
- 本カタログは最小セットであり、プロダクト特性に応じて拡張してよい。
