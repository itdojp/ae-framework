# AGENTS — Multi‑Agent作業ルール（ae-framework）

このドキュメントは、リポジトリ内でエージェントが安全かつ一貫した方法で作業するためのガイドです。

## 目的
- CI 安定化・段階導入（Verify Lite 必須、その他はラベル駆動）
- 小さく安全な PR を多数（revert しやすい粒度）
- actionlint 準拠（echo→printf、GITHUB_OUTPUT/GITHUB_ENV は printf で追記）

## ブランチ/PR運用
- ブランチ名: `chore/ci-<topic>-<short>`（例: `chore/ci-actionlint-printf-2`）
- PR ラベル:
  - `run-qa`: ae-ci の `qa-bench` を実行
  - `run-security`: Security/SBOM 系を実行
  - `ci-non-blocking`: 非ブロッキングで実行（continue-on-error）
  - `enforce-security`: Security しきい値を強制
  - `coverage:<pct>`: coverage-check のしきい値上書き

## テスト/検証
- ローカル: `corepack enable && pnpm i && pnpm build`
- 速い確認: `pnpm run test:fast`（CI と同一の除外設定）
- QA 軽量: `node dist/src/cli/index.js qa --light`（または `pnpm tsx src/cli/qa-cli.ts --light`）
- actionlint: `uses: rhysd/actionlint@v1.7.1`（CI で workflow-lint.yml が実行）

## ワークフロー変更ポリシー
- echo→printf へ置換（特に `>> $GITHUB_OUTPUT` / `$GITHUB_ENV` は `printf` + 変数引用）
- paths / labels による発火制御（重い作業は opt-in）
- SBOM/セキュリティは PR 既定非必須、ラベル/変数で段階導入

## Slash Commands（GitHub コメントでの即時連携）
- PR コメントで以下を投稿すると、ラベル付与などを自動化します（.github/workflows/agent-commands.yml）。
  - `/run-qa` … `run-qa` ラベル付与（ae-ci の QA 実行）
  - `/run-security` … `run-security` ラベル付与（Security/SBOM 実行）
  - `/run-hermetic` … `run-hermetic` ラベル付与（Hermetic CI 実行）
  - `/run-spec` … `run-spec` ラベル付与（Spec Fail-Fast 実行）
  - `/run-drift` … `run-drift` ラベル付与（Codegen Drift 検出 実行）
  - `/non-blocking` … `ci-non-blocking` ラベル付与（一部ジョブを continue-on-error）
  - `/blocking` … `ci-non-blocking` ラベル除去（通常のブロッキング設定へ）
  - `/ready` … `do-not-merge` ラベル除去（マージ待ち状態へ）
  - `/pr-digest` … `pr-summary:digest` ラベル付与（要約）
  - `/pr-detailed` … `pr-summary:detailed` ラベル付与（詳細）
  - `/handoff A|B|C` … ハンドオフ用ラベル `handoff:agent-a|b|c` を付与し、次エージェントに委譲
  - `/enforce-typecov` … `enforce-typecov` ラベル付与（型カバレッジのしきい値 enforcement）
  - `/coverage <pct>` … `coverage:<pct>` ラベル設定（既存の coverage:* を置換）
  - バッチ系（CI Fast の任意カテゴリ実行、いずれもラベル付与）
    - `/qa-batch-commands` または `/run-qa:commands` … `qa-batch:commands`
    - `/qa-batch-cli` または `/run-qa:cli` … `qa-batch:cli`
    - `/qa-batch-property` または `/run-qa:property` … `qa-batch:property`
    - `/qa-batch-agents` または `/run-qa:agents` … `qa-batch:agents`
  - ディスパッチ（workflow_dispatch 直起動）
    - `/verify-lite` … verify-lite.yml を PR の head ブランチで起動
    - `/run-qa-dispatch` … ae-ci.yml を PR の head ブランチで起動
    - `/run-security-dispatch` … sbom-generation.yml を PR の head ブランチで起動
    - `/ci-fast-dispatch` … ci-fast.yml を PR の head ブランチで起動（対応ラベルが付くとバッチも実行）
    - `/formal-verify-dispatch` … formal-verify.yml を PR の head ブランチで起動
    - `/run-flake-dispatch` … flake-detect.yml を PR の head ブランチで起動
    - `/spec-validation-dispatch` … spec-validation.yml を PR の head ブランチで起動
  - フォーマル/契約（ラベル付与）
    - `/run-formal` … `run-formal` を付与（verify/formal 系スタブを非ブロッキングで実行）
    - `/enforce-formal` … `enforce-formal` を付与（有効時にエンフォース）
    - `/enforce-contracts` … `enforce-contracts` を付与（有効時にエンフォース）

## 参考ファイル
- `.github/workflows/ae-ci.yml`: PR 時 QA/Bench 軽量モード
- `.github/workflows/sbom-generation.yml`: SBOM/依存監査/閾値強制
- `docs/ci-policy.md`: ポリシー集約
- `SECURITY.md`: セキュリティ運用（ラベル/変数）

## 作業の進め方（共通）
1) 変更箇所を最小限に限定する
2) CI に影響のある変更は `run-qa` ラベルで限定的に回す
3) テキスト生成・整形系は printf で統一
4) 変更後: `pnpm -s types:check && pnpm -s build` のローカル通過を目安
