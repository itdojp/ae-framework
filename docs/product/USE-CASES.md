# ae-framework 典型的な利用シナリオ（Use Cases）

> Language / 言語: English | 日本語

---

## English (Summary)

This document lists typical ae-framework usage scenarios with concrete commands, expected artifacts, and CI operation tips.

---

## 日本語

このドキュメントは「実行シナリオ中心」です。導入判断（どのプロダクトに何を入力し、何が出力されるか／どのツールが適するか）は `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md` を参照してください。

## 0. 前提: 実行モード（ローカル/CI）

### 0.1 開発時（TypeScript実行）
`src/cli/index.ts` を直接実行するため、コマンドは以下の形式を推奨します。

```bash
pnpm run ae-framework -- <command> [args...]
```

### 0.2 ビルド済みCLI（配布物）
`package.json bin` が `dist/src/cli/*` を指すため、ビルド後は以下を利用します。

```bash
pnpm run build
pnpm exec ae --help
```

### 0.3 CI（GitHub Actions）
主要ワークフローは `.github/workflows/*` に定義されています。PR運用では `Verify Lite / verify-lite` と `Copilot Review Gate / gate` を基本ゲートとする前提が一般的です。

---

## 1. PR運用（最頻出）: verify-lite + Copilot Review Gate で最小ゲートを回す

### 目的
レビューと軽量検証を最短で回し、マージ条件（必須チェック）を満たした状態で取り込む。

### 手順（PR作成〜マージ）
1) PRを作成  
2) GitHub Copilot のレビューを付与（Copilot Review Gate の前提）  
3) 指摘対応:
   - `suggestion` を取り込む/不要なら理由をコメント
   - Copilotが関与したスレッドを **Resolve conversation** で解決  
4) 追加検証（必要時）  
   - PRコメントで `/verify-lite` を実行（`.github/workflows/agent-commands.yml`）  
   - 追加で `/review strict`（coverage等の追加検証）も選択可能
5) 必須チェックがGreenになったらマージ

### オプション（自動化）
- Copilot suggestion の自動適用（auto-fix）: `AE_COPILOT_AUTO_FIX=1`（Repository Variables）。詳細: `docs/ci/copilot-auto-fix.md`
- auto-merge の自動有効化（auto-merge）: `AE_AUTO_MERGE=1`（Repository Variables）。詳細: `docs/ci/auto-merge.md`
- PR 自動化の運用全体像: `docs/ci/pr-automation.md`

### 期待される成果物（代表）
- `artifacts/verify-lite/verify-lite-run-summary.json`（verify-liteの要約; `VERIFY_LITE_SUMMARY_FILE` で出力先を制御）
- `artifacts/verify-lite/verify-lite-lint-summary.json`（verify-lite lintの要約; CIのbaseline比較に使用）

### 注意点（根拠）
- Copilot Review Gate は「Copilotレビューの存在」と「Copilotが関与したスレッドの解決」を要求します（`docs/ci/copilot-review-gate.md` / `.github/workflows/copilot-review-gate.yml`）。

---

## 2. リポジトリ管理（導入時）: Branch protection を preset で適用する

### 目的
Required checks を標準化し、プロジェクト横断で同一運用に揃える。

### 手順
1) preset JSON を選定（例）:
   - `.github/branch-protection.main.verify-lite-noreview.json`（verify-lite必須・レビュー要件なし）
2) admin scope のトークンで適用（`scripts/admin/apply-branch-protection.mjs`）

```bash
ADMIN_TOKEN=ghp_xxx \
REPO=itdojp/ae-framework \
BRANCH=main \
node scripts/admin/apply-branch-protection.mjs .github/branch-protection.main.verify-lite-noreview.json
```

### 注意点（根拠）
- `ADMIN_TOKEN`（または `GITHUB_TOKEN`）が必要で、repo admin scope が要求されます（`scripts/admin/apply-branch-protection.mjs` のUsage/エラーメッセージ）。

---

## 3. 仕様運用: AE-Spec（Markdown）→ AE-IR（JSON）→ lint / export

### 目的
人間/エージェントが書く仕様（Markdown）を機械可読（AE-IR JSON）に変換し、品質検査や外部形式へのエクスポートに接続する。

### 手順（最小）
1) AE-Spec を用意（例: `spec/example-spec.md`）  
2) validate（compile + lint）を実行（`src/cli/spec-cli.ts`）

```bash
pnpm run ae-framework -- spec validate -i spec/example-spec.md --output .ae/ae-ir.json
pnpm run ae-framework -- spec lint -i .ae/ae-ir.json

# CI 向け機械可読レポート
pnpm run ae-framework -- spec validate -i spec/example-spec.md --output .ae/ae-ir.json --format json --report-output artifacts/spec/validate-report.json
pnpm run ae-framework -- spec lint -i .ae/ae-ir.json --format json --output artifacts/spec/lint-report.json
# schema: schema/spec-validation-report.schema.json
```

3) （任意）外部形式へ export

```bash
pnpm run ae-framework -- spec export -i .ae/ae-ir.json --format kiro
```

### 成果物（代表）
- `.ae/ae-ir.json`（AE-IR）
- export の出力ディレクトリ（デフォルトは `.kiro/specs/<spec-id>/`）

---

## 4. 形式検証（必要時）: 反例→失敗テスト→修正→Green の最小ループ

### 目的
仕様の矛盾や境界条件を、形式手法（TLA+/SMT/Alloy 等）とテストの往復で閉じる。

### 手順（例）
1) ツール前提の確認（存在チェック; non-blocking）
```bash
pnpm run tools:formal:check
```

2) 形式検証（全体まとめて実行）
```bash
pnpm run verify:formal
```

3) 出力要約の確認（運用は runbook を参照）
- `docs/quality/formal-runbook.md`

### 注意点
- ローカルでの実行可否は環境（TLC/Apalache/SMTソルバ等の導入）に依存します。導入手順は `docs/quality/formal-tools-setup.md` を参照してください。

---

## 5. 退行検知（重いテスト）: 成果物キャッシュとトレンド比較

### 目的
Mutation/MBTなどの重い検証をキャッシュし、差分（退行・改善）を機械的に比較して意思決定を高速化する。

### 手順（例）
```bash
# 直近結果をキャッシュへ保存
node scripts/pipelines/sync-test-results.mjs --store

# スナップショット生成（CIトリアージ用）
node scripts/pipelines/sync-test-results.mjs --snapshot

# トレンド比較（JSON出力）
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

### 成果物（代表）
- `reports/heavy-test-trends.json`
- `.cache/test-results`（運用により配置/復元）

---

## 6. セキュリティ/SBOM（必要時）: opt-in で強化ゲートを走らせる

### 目的
通常PRは軽量に保ちつつ、必要時のみセキュリティ監査やSBOM生成を起動する。

### 手順（ローカル例）
```bash
pnpm run security:integrated:quick
```

### 手順（PR例: ラベル/Slashコマンド）
- PRコメントで `/run-security`（`.github/workflows/agent-commands.yml`）→ `run-security` ラベル付与  
- 追加で `/run-security-dispatch` により workflow_dispatch を起動する運用も可能

---

## 7. エージェント統合（CodeX）: playbook で Setup→QA→（任意）Formal を回す

### 目的
外部オーケストレータ（CodeX等）でフェーズを段階実行し、`artifacts/ae/context.json` に実行ログ/成果物パスを集約して継続運用を容易にする。

### 手順（最小）
```bash
pnpm run codex:run
```

### 発展（Formalを含める）
```bash
node scripts/codex/ae-playbook.mjs --enable-formal --formal-timeout=60000
```

### 参考（根拠）
- 設計と運用詳細: `docs/codex/ae-playbook.md`
- CodeX統合: `docs/integrations/CODEX-INTEGRATION.md`
