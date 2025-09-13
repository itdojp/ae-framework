# CI ポリシー（暫定運用）

本ドキュメントは、PR の体験を改善しつつ品質を担保するための CI 方針です。

## 目的
- PR では軽量かつ決定的な検査のみをブロッキング（必須）にする
- 重い/不安定な検査はラベルやパスに応じてオプトイン実行
- main への push や定期実行で包括的な検査を行い、品質を継続保証

## 必須チェック（PR ブロッキング）
- Verify Lite（types:check / lint / build）
- 必要に応じて validate-artifacts-ajv / coverage gate を追加

## オプトイン用ラベル
- `run-spec`: 仕様 Fail-Fast を PR で有効化
- `run-drift`: Codegen Drift 検出を PR で有効化
- `run-hermetic`: Hermetic CI を PR で有効化
- `run-security`: SBOM/Security を PR で有効化
- `run-quality`: quality 系テスト（Parallel Test matrix の quality）を PR で有効化
- `run-flake`: flake-detection を PR で有効化
- `run-e2e`: E2E テストを PR で有効化

## パス条件
- 仕様関連の変更（`spec/**`, `.ae/**`）のみ Fail-Fast を発火
- 依存やコード大変更時のみ SBOM/Security を発火

## 運用メモ
- 緊急時は `ci-non-blocking` ラベルで一部ワークフローを非ブロッキング化
- マージ後は main の包括的 CI（夜間/週次含む）でカバー
- 必須チェックは基本的に Verify Lite 中心にし、他は非必須

