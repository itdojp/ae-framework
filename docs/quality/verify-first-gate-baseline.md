---
docRole: derived
canonicalSource:
- docs/quality/verify-first-implementation-runbook.md
- policy/risk-policy.yml
lastVerified: '2026-03-21'
---
# Verify-first 最小Quality Gate基準（Required / Opt-in）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

Define the minimal required gate baseline for day-to-day PR handling and the opt-in expansion gates used by Verify-first operations.

### 2. Required Gates (PR blocking)

| Gate | Minimum success condition | Primary evidence |
| --- | --- | --- |
| `verify-lite` | `types:check / lint / build / conformance` succeed | `artifacts/verify-lite/verify-lite-run-summary.json` |
| `policy-gate` | risk policy, required labels, topology / approval conditions succeed | `artifacts/ci/policy-gate-summary.json` |
| `Copilot Review Gate / gate` | required review gate succeeds and no AI review thread remains unresolved | Copilot Review Gate logs |

Notes:
- Treat `docs/ci-policy.md` as the current operational source for detailed CI policy.
- Required gates should stay fast, deterministic, and reproducible.
- `test:fast` is a recommended local smoke check, but it is not itself a PR-blocking required gate.

### 3. Opt-in Gates (expansion)

| Gate family | Typical label / trigger | When to apply | Primary evidence |
| --- | --- | --- | --- |
| Formal | `run-formal`, `enforce-formal` | spec alignment, formal verification, semantic regression risk | `artifacts/hermetic-reports/formal/**` |
| Security | `run-security` | dependency updates, auth / authz changes, secret handling | security / sbom reports |
| Adapters | `run-adapters` | a11y, perf, lighthouse, browser-facing quality checks | adapter summaries / comments |
| QA | `run-qa` | behavior regression or performance degradation concerns | QA / benchmark reports |

Contract separation notes:
- API / integration contract verification such as Pact belongs to `run-integration` or the extended CI lane.
- DbC concerns are covered through a combination of property checks, runtime conformance, and integration assertions.

### 4. Decision Rules

1. Run the required gates for every PR.
2. Add opt-in gates according to the nature and risk of the change.
3. Even when an opt-in gate is not run, keep the rationale recordable in the PR.
4. If a required gate must fail-open, record the exception reason and a follow-up issue.

### 5. Failure Diagnostics

Use the following template when a required or opt-in gate fails:
- `docs/quality/verify-first-failure-diagnostic-template.md`

The diagnostic record should preserve reproducibility, not only narrative explanation.

### 6. References

- `docs/ci-policy.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/quality/formal-runbook.md`
- `docs/quality/verify-first-failure-diagnostic-template.md`

---

## 日本語

### 1. 目的

Verify-first を運用可能にするため、PRで常時適用する最小ゲート（Required）と、必要時に有効化する拡張ゲート（Opt-in）を定義します。

### 2. Required ゲート（PRブロッキング）

| ゲート | 合否基準（最小） | 主な証跡 |
| --- | --- | --- |
| `verify-lite` | `types:check / lint / build / conformance` が成功 | `artifacts/verify-lite/verify-lite-run-summary.json` |
| `policy-gate` | risk policy, required labels, topology/approval 条件が成功 | `artifacts/ci/policy-gate-summary.json` |
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
