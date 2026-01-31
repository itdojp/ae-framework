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

## 2. 前提条件（根拠）
- Node.js: `>=20.11 <23`（`package.json` の `engines.node`）
- pnpm: `10.0.0`（`package.json` の `packageManager`）
- GitHub Actions 利用可能なリポジトリ

## 3. セットアップ

### 3.1 依存関係の導入
```bash
pnpm install
```

### 3.2 開発フックの導入
```bash
pnpm run setup-hooks
```

### 3.3 最小検証
```bash
pnpm run lint
pnpm run test:fast
```

## 4. 基本ワークフロー

### 4.1 仕様の登録と検証
- 仕様の配置: `spec/`（詳細は `docs/spec/registry.md`）
- 検証コマンド:
```bash
pnpm run spec:lint
pnpm run spec:validate
```

### 4.2 形式検証（任意）
前提: `docs/quality/formal-tools-setup.md` に従いツールを準備します。

```bash
pnpm run verify:formal
```

### 4.3 テスト実行
```bash
pnpm run test:fast
pnpm run test:unit
pnpm run test:int
```

必要に応じて、`pnpm run pbt` や `pnpm run bdd` を追加します。

### 4.4 CI運用の基本
- PR作成時に verify-lite を基本ゲートとします
- Branch protection の Required checks では、`Verify Lite / verify-lite` と `Copilot Review Gate / gate` を必須化する運用が想定されています（詳細: `docs/ci/branch-protection-operations.md`, `docs/ci/copilot-review-gate.md`）
- 必要に応じて `ci-extended` や `formal-verify` を追加実行します
- 詳細: `docs/ci/branch-protection-operations.md`, `docs/quality/formal-runbook.md`

## 5. CLI利用の基本

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
pnpm run ae-framework -- help
pnpm run ae-framework -- spec --help
pnpm run ae-framework -- quality run --env development
pnpm run ae-framework -- security --help
pnpm run ae-framework -- conformance --help
pnpm run ae-framework -- integration --help
pnpm run ae-framework -- resilience --help
pnpm run ae-framework -- sbom --help
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

# 依存監査
pnpm run security:integrated:quick
```

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
- 全体ナビゲーション: `docs/README.md`
