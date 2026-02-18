# ae-framework 利用マニュアル

> Language / 言語: English | 日本語

---

## English (Summary)

This manual explains setup, common workflows, and operational commands for ae-framework.

---

## 日本語

## 1. 対象読者
- プロダクト開発者、QA、運用担当
- 仕様検証やCI品質ゲートを運用するチーム
- エージェント統合を検討しているチーム
- 導入対象の見極め（入力/出力/ツール適性）を行いたいチーム

適用判断の全体像は `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md` を参照してください。

## 2. 前提条件（根拠）
- Node.js: `>=20.11 <23`（`package.json` の `engines.node`）
- pnpm: `10.0.0`（`package.json` の `packageManager`）
- `npm install` は `preinstall` ガードで失敗させる仕様（pnpm workspace 前提）
- GitHub Actions 利用可能なリポジトリ
- `verify:lite` をそのまま利用する場合は JS/TS ツールチェーン前提（`pnpm types:check`, `pnpm lint`, `pnpm run build`。CI の Verify Lite ワークフローではこれに加えて `vitest` が実行されます）
- 非JS/TSプロダクトは `verify:formal` / `verify:conformance` を先行導入し、lint/test/build は対象言語向けジョブを別途定義
- Windows は PowerShell でも実行可能ですが、ツール互換性で問題が出る場合は WSL2 を推奨

## 3. セットアップ

### 3.1 依存関係の導入
```bash
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install
```

`npm install` を実行した場合は、pnpm へ移行するためのエラーメッセージを表示して即時終了します（exit 1）。

### 3.2 初回1コマンド（推奨）
```bash
pnpm run first-run
```

`doctor:env -> build -> verify:lite` を順に実行し、実行結果を以下に保存します。
- artifacts/first-run 配下の summary JSON（機械可読）
- artifacts/first-run 配下の summary Markdown（人間向け）
- artifacts/first-run/logs 配下のログ（各ステップ）

終了コード契約:
- `0`: すべてのステップが成功
- `1`: いずれかの必須ステップが失敗
- `3`: 引数不正
- `4`: サマリ書き込み失敗

### 3.3 環境診断（個別実行）
```bash
pnpm run doctor:env
```

診断結果は `artifacts/doctor/env.json` に保存されます。終了コード契約:
- `0`: 必須チェックすべてOK
- `2`: 警告あり（例: `dist/` 未生成、corepack未検出）
- `1`: 要修正（例: Node.js範囲外、pnpm未導入）
- `3`: 引数不正（例: 未定義オプション）

### 3.4 開発フックの導入
```bash
pnpm run setup-hooks
```

### 3.5 最小検証
```bash
pnpm run lint
pnpm run test:fast
```

### 3.6 設定ファイル（任意）
CLIは YAML 設定を探索して読み込みます（`src/cli/config/ConfigLoader.ts`）。

探索順（上から優先）:
- `config/ae-framework.yml`
- `config/ae-framework.yaml`
- `ae-framework.yml`
- `ae-framework.yaml`
- `.ae-framework.yml`
- `.ae-framework.yaml`

設定ファイルが存在しない場合は、デフォルト設定で動作します。

## 4. 基本ワークフロー

### 4.1 仕様の登録と検証
- 仕様の配置: `spec/`（詳細は `docs/spec/registry.md`）
- 検証コマンド（例: `spec/example-spec.md`）:
```bash
# AE-Spec (Markdown) -> AE-IR (JSON)
pnpm run spec:validate -i spec/example-spec.md --output .ae/ae-ir.json

# AE-IR lint
pnpm run spec:lint -i .ae/ae-ir.json

# CI向け JSON レポート（schema/spec-validation-report.schema.json 準拠）
pnpm run ae-framework -- spec lint -i .ae/ae-ir.json --format json --output artifacts/spec/lint-report.json
pnpm run ae-framework -- spec validate -i spec/example-spec.md --output .ae/ae-ir.json --format json --report-output artifacts/spec/validate-report.json
```

### 4.2 形式検証（任意）
前提: `docs/quality/formal-tools-setup.md` に従いツールを準備します。

```bash
pnpm run verify:formal
```

#### CSP(cspx) を利用する場合（推奨）
`verify:csp` は `cspx` を優先バックエンドとして利用できます。

```bash
# 再現性のため commit pin で導入
cargo install --git https://github.com/itdojp/cspx --rev 8a67639ea4d3f715e27feb8cd728f46866a905db --locked cspx

# 機能確認（summary-json 対応）
cspx --version
cspx typecheck --help | grep -- --summary-json

# smoke 実行
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck
```

確認ポイント:
- `artifacts/hermetic-reports/formal/csp-summary.json` が生成される
- `artifacts/hermetic-reports/formal/cspx-result.json` が生成される
- `csp-summary.json` の `backend/status/resultStatus/exitCode` が記録される

### 4.3 テスト実行
```bash
pnpm run test:fast
pnpm run test:unit
pnpm run test:int
```

必要に応じて、`pnpm run pbt` や `pnpm run bdd` を追加します。`pbt` は `--config`（最優先）→ `PBT_CONFIG` 環境変数 → `tests/property/vitest.config.*` → `tests/property` ディレクトリの順で解決します。解決不能時は `PBT_CONFIG_NOT_FOUND`（exit 2）、`pnpm` 非導入環境では exit 127 になります。

### 4.4 CI運用の基本
- PR作成時に verify-lite を基本ゲートとします
- Branch protection の Required checks では、`Verify Lite / verify-lite` と `Copilot Review Gate / gate` を必須化する運用が想定されています（詳細: `docs/ci/branch-protection-operations.md`, `docs/ci/copilot-review-gate.md`）
- （任意）Copilot suggestion の自動適用（auto-fix）を有効化できます（プロジェクト単位のRepository Variables）。詳細: `docs/ci/copilot-auto-fix.md`
- （任意）auto-merge を自動有効化し、人手マージを省略する運用にできます（プロジェクト単位のRepository Variables）。詳細: `docs/ci/auto-merge.md`
- PR 自動化（Copilot→auto-fix→auto-merge）の運用全体像: `docs/ci/pr-automation.md`
- 必要に応じて `ci-extended` や `formal-verify` を追加実行します
- 詳細: `docs/ci/branch-protection-operations.md`, `docs/quality/formal-runbook.md`

## 5. CLI利用の基本
実行モードの使い分けは `docs/product/COMMAND-MODES.md` を参照してください。

### 5.1 開発時のCLI確認
```bash
pnpm run ae-framework -- --help
```

### 5.2 ビルド後のCLI
ビルド後に `ae` または `ae-framework` を利用します（`package.json bin` が `dist/src/cli/*` を指します）。
```bash
pnpm run build
pnpm exec ae --help
# または
pnpm exec ae-framework --help
```

CLIの詳細は `docs/reference/CLI-COMMANDS-REFERENCE.md` を参照してください。

### 5.3 代表的なCLIサブコマンド（開発時）
開発時（TypeScript実行）は `pnpm run ae-framework -- <command>` を使用します。

```bash
pnpm run ae-framework -- --help
pnpm run ae-framework -- spec --help
pnpm run ae-framework -- quality run --env development
pnpm run ae-framework -- quality run --env development --no-history
pnpm run ae-framework -- security --help
pnpm run ae-framework -- conformance --help
pnpm run ae-framework -- integration --help
pnpm run ae-framework -- resilience --help
pnpm run ae-framework -- sbom --help
```

### 5.4 CLI契約（exit code / JSONエラー）
- `0`: 正常終了
- `2`: 不正入力・契約違反（例: 不正サブコマンド、必須引数不足）
- `1`: 内部エラー・想定外の失敗

`spec lint` / `spec validate` で `--format json` を指定した場合、失敗時も JSON を返します。  
例（失敗時）:

```json
{
  "error": true,
  "code": "SPEC_INVALID_INPUT",
  "message": "ENOENT: no such file or directory, open 'spec/does-not-exist.json'",
  "details": {
    "input": "spec/does-not-exist.json"
  },
  "ts": "2026-02-18T00:00:00.000Z",
  "command": "lint"
}
```

## 6. エージェント統合
- CodeX 連携: `docs/integrations/CODEX-INTEGRATION.md`
- Claude Code 連携: `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`
- Playbook 実行例: `pnpm run codex:run`

## 7. 代表的な運用コマンド

```bash
# 形式検証サマリ
pnpm run formal:summary

# 仕様ツールのチェック
pnpm run spec:validate

# CI向け最小検証
pnpm run verify:lite

# fast/full を統一実行（JSONサマリ出力）
pnpm run verify:profile -- --profile fast --json --out artifacts/verify-profile-summary.json

# Issue要件ID起点のトレーサビリティ（抽出 -> matrix -> strict validate）
pnpm run ae-framework -- traceability extract-ids --issue "https://github.com/<org>/<repo>/issues/1" --pattern "(?:LG|REQ)-[A-Z0-9_-]+" --output docs/specs/issue-traceability-map.json
pnpm run ae-framework -- traceability matrix --map docs/specs/issue-traceability-map.json --tests "tests/**/*" --code "src/**/*" --format json --output docs/specs/ISSUE-TRACEABILITY-MATRIX.json
pnpm run ae-framework -- validate --traceability --strict --sources docs/specs/ISSUE-TRACEABILITY-MATRIX.json

# 有用性評価レポート（JSON + Markdown）
pnpm run evaluate:usefulness -- --strict-inputs --min-score 70

# 依存監査
pnpm run security:integrated:quick
```

補足:
- Full smoke は `pnpm run verify:formal`
- Formal ツールの導入状況確認は `pnpm run tools:formal:check`
- CSP 詳細手順は `docs/quality/formal-csp.md`
- Issue要件IDトレーサビリティ手順は `docs/quality/issue-requirements-traceability.md`
- 有用性評価の入力契約・スコア算出規約は `docs/quality/usefulness-evaluation.md`

## 8. トラブルシューティング

### 8.1 verify-lite ゲートの失敗
- `Verify Lite / verify-lite` が Required の場合、まず `verify-lite` のログ/サマリを確認
- `Copilot Review Gate / gate` が Required の場合、Copilotのレビューが存在し、**Copilotが関与したスレッドがすべて解決済み**かを確認（PR画面で「Resolve conversation」）
- `docs/ci/ci-troubleshooting-guide.md` を参照
  - Copilot Review Gate の詳細: `docs/ci/copilot-review-gate.md`

### 8.2 Node バージョン不一致
- `node -v` を確認し、`>=20.11 <23` の範囲に調整

### 8.3 形式検証ツール不足
- `docs/quality/formal-tools-setup.md` を参照して導入

## 9. 参考資料
- 概要説明資料: `docs/product/OVERVIEW.md`
- 詳細説明資料: `docs/product/DETAIL.md`
- 適用対象・入力/出力・ツール適性: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- コマンド体系（実行モード別）: `docs/product/COMMAND-MODES.md`
- 実装準拠の全体構成: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- 全体ナビゲーション: `docs/README.md`
