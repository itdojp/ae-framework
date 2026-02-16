# Verify-first 最小Quality Gate基準（Required / Opt-in）

> Language / 言語: English | 日本語

---

## English (Summary)

Defines a minimal required gate baseline and opt-in expansion gates for Verify-first operations, plus when to apply each gate.

---

## 日本語

### 1. 目的

Verify-first を運用可能にするため、PRで常時適用する最小ゲート（Required）と、必要時に有効化する拡張ゲート（Opt-in）を定義します。

### 2. Required ゲート（PRブロッキング）

| ゲート | 合否基準（最小） | 主な証跡 |
| --- | --- | --- |
| `verify-lite` | `types:check / lint / build / conformance` が成功 | `artifacts/verify-lite/verify-lite-run-summary.json` |
| `Quality Gates (development profile)` | 開発プロファイル向け Quality Gates が成功 | Quality Gates ログ |
| `Copilot Review Gate / gate` | チェックが成功し、未処理レビューコメントがない | Copilot Review Gate ログ |

補足:
- 詳細ポリシーは `docs/ci-policy.md` を正とする。
- 必須ゲートは「高速・決定的・再現可能」を優先する。
- `test:fast` は推奨の高速テスト実行だが、PRブロッキング要件ではない。

### 3. Opt-in ゲート（拡張）

| ゲート群 | 代表ラベル/起動 | 適用の目安 | 主な証跡 |
| --- | --- | --- | --- |
| Formal | `run-formal`, `enforce-formal` | 仕様整合/形式検証が必要な変更 | `artifacts/hermetic-reports/formal/**` |
| Security | `run-security` | 依存更新、認証/認可、機密情報処理の変更 | security/sbom レポート |
| Adapters | `run-adapters` | a11y/perf/lighthouse 等の品質確認 | adapter summary/comment |
| QA | `run-qa` | 挙動回帰や性能劣化の懸念がある変更 | qa bench レポート |

補足（contract の意味分離）:
- API/Integration contract 検証（Pact）は `run-integration` / CI Extended の `pipelines:pact` を参照する。
- DbC（pre/post/invariant）は、property / runtime conformance / integration assertion の組み合わせで担保する。

### 4. 適用基準（判断ルール）

1. すべてのPRで Required ゲートを実施する。  
2. 変更の性質に応じて Opt-in を追加する。  
3. Opt-in未実施でも、理由をPRに記載できる状態を維持する。  
4. Required を fail-open する場合は、例外理由とフォローアップIssueを必須化する。

### 5. 失敗時診断テンプレート

失敗時は以下テンプレートを使用し、再現性のある診断を残します。  
`docs/quality/verify-first-failure-diagnostic-template.md`

### 6. 参照

- `docs/ci-policy.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/quality/formal-runbook.md`
- `docs/quality/verify-first-failure-diagnostic-template.md`
