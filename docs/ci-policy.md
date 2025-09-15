# CI Policy (Fast/Stable by Default)

目的: 開発者体験と安定性を最大化するため、PR では軽量・安定な検査のみデフォルト実行とし、重い/任意の検査はラベルで opt-in する。

必須チェック（main, PR）
- Verify Lite / verify-lite（types:check, lint, build）

ラベル運用
- `ci-non-blocking`: 一部ジョブ（traceability, model-check, contracts, security 等）を continue-on-error で実行し、PRをブロックしない。
- `run-qa`: `ae-ci` ワークフローの `qa-bench` を PR で実行（デフォルトは非実行）。
- `run-security`: `security` ワークフローの重い検査（Security Scanning, Dependency Audit, License Compliance, CodeQL 等）を PR で実行（デフォルトは非実行）。
- `coverage:<pct>`: coverage-check のしきい値を上書き（既定 80）。例: `coverage:75`

test:fast（Fast CI スイート）
- 目的: Resilience/主要ユニットと軽量統合を即時検証。重い/環境依存テストは除外。
- 現状の主な除外: examples/**, **/__e2e__/**, tests/examples/**, tests/docker/**, tests/a11y/**, tests/property/**, tests/traceability/**, tests/security/**, tests/contracts/**, tests/utils/**, tests/integration/**, tests/resilience/integration.test.ts, tests/conformance/**, tests/cegis/**, tests/cli/**, tests/commands/**, tests/api/**, tests/tdd-setup.test.ts
- 再導入方針: 小PRでカテゴリ毎に緑化→解除。失敗時は即 revert 可能な粒度。

セキュリティ/コンプライアンス
- デフォルトは PR で非実行（`run-security` ラベル時のみ実行）。結果は artifacts に集約。
- 必須化・閾値強化は段階導入（別Issueで合意のうえ切替）。

注意
- CIに関する変更は基本的に小PRで段階導入・段階強化。
- 運用の詳細は今後もこの文書を更新する。

