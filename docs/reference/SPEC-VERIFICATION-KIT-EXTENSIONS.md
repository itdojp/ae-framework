# Spec & Verification Kit Extensions (Draft)

## 目的
- Spec & Verification Kit の中長期拡張項目を整理し、導入順と最小要件を明示する。
- AI/エージェント活用時に「証拠が残る拡張」へ優先投資する。

## 拡張の優先順位（案）
1. **Model Checking 入口**
   - TLA+ / Alloy の最小テンプレートと実行手順を用意する
   - 成果物: `specs/formal/` のテンプレート、`docs/quality/formal-runbook.md` の補足
2. **Conformance / Traceability 連携**
   - Trace/Envelope からモデルチェック結果を結び付ける
   - 成果物: `docs/trace/` のリンク整備、`scripts/formal/` のサマリ出力拡張
3. **Verifier Adapter Layer**
   - TLC / Apalache / Kani などを統一CLIで呼び出す
   - 成果物: `scripts/verify/` の統合CLI / profile設計（例: `verify:formal`）
4. **Policy/Contract 強化**
   - Cedar/OPA などのポリシー検証を Spec Kit の標準オプションへ
   - 成果物: `specs/policy/` テンプレート、AJV/OPA 実行テンプレート

## 最小要件（各拡張のゴール）
- **テンプレート**: コピーして使える雛形（Spec/Tests/Runbook）
- **コマンド**: `pnpm run` または `node scripts/...` で実行可能
- **CI**: `docs/templates/ci/` に workflow snippet を用意
- **証跡**: 出力物の配置ルール（`artifacts/` or `reports/`）

## 既存資産との対応
- `docs/quality/formal-runbook.md` / `docs/quality/formal-gates.md`
- `specs/formal/`（TLA+/Alloy）
- `scripts/formal/verify-conformance.mjs`
- `docs/trace/*` / `scripts/trace/*`

## 次のタスク（案）
- TLA+ / Alloy の最小テンプレを `specs/formal/` に追加
- Model checking の実行サンプルを `docs/quality/formal-runbook.md` に追記
- Traceability と model check の結合例を `docs/trace/` に記載
