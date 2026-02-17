# Phase 0 Inventory (2026-02-17)

Issue: #2031  
目的: Phase 1 以降の整理作業に先立ち、現行構成を可視化して分類基準を確定する。

## 1. スナップショット（集計）

- 集計日: 2026-02-17
- `.github/workflows`: **51**
- `scripts`（`.mjs/.js/.ts`）: **198**
- `src` 内 `any`: **1166**
- `TODO/FIXME`（`src/scripts/tests/docs`）: **141**

追跡ファイル上位ディレクトリ（件数）:

1. `tests` 614
2. `docs` 361
3. `src` 292
4. `artifacts` 289
5. `scripts` 270

## 2. ルート直下の分類

### 2.1 keep（維持）

- 開発/運用の中核:
  - `src/`, `tests/`, `docs/`, `scripts/`, `spec/`, `schema/`
  - `.github/`, `config/`, `configs/`, `packages/`, `apps/`
- プロジェクトメタ:
  - `README.md`, `LICENSE`, `CONTRIBUTING.md`, `SECURITY.md`, `AGENTS.md`
  - `package.json`, `pnpm-lock.yaml`, `pnpm-workspace.yaml`, `tsconfig.json`

### 2.2 safe-remove（削除/クリーン対象）

- ルート直下に出力される一時生成物:
  - `cegis-report-*.json`
  - `generated-*.json`
  - `filtered-test.json`, `parallel-test.json`, `run-suite.json`, `run-test.json`, `workflow-test.json`
  - `conformance-results.json`, `verify-lite-run-summary.json`, `verify-lite-lint-summary.json`, `verify-lite-lint.log`
- 再生成可能ディレクトリ:
  - `node_modules/`, `coverage/`, `test-results/`, `test-results-run/`, `tmp/`

### 2.3 needs-review（要判断）

- `artifacts/`（追跡済み成果物が多く、削除/移動は参照調査が必要）
- `reports/`, `temp-reports/`（保存方針と保持期間の明文化が必要）
- `proofs/`, `plans/`, `examples/`（継続利用有無の整理が必要）
- `_apalache-out/`（用途・再生成性の確認が必要）

## 3. 生成物の発生源（確認済み）

| 生成物 | 発生源（コード/コマンド） | 備考 |
|---|---|---|
| `cegis-report-*.json` | `src/cegis/auto-fix-engine.ts` | ルート出力。移設方針が必要 |
| `conformance-results.json` | `src/cli/conformance-cli.ts` default output | 既定値の見直し対象 |
| `generated-*.json`, `run-*.json` | integration CLI/tests | テスト実行後のクリーン対象 |
| `artifacts/verify-lite/verify-lite-lint-summary.json` | `scripts/ci/run-verify-lite-local.sh` | ルート出力は禁止。`artifacts/verify-lite/` に統一 |

## 4. コード改善候補（優先観測）

### 4.1 巨大ファイル（行数上位）

1. `src/agents/code-generation-agent.ts` (1377)
2. `src/cli/conformance-cli.ts` (1374)
3. `src/agents/intent-agent.ts` (1343)
4. `src/utils/enhanced-state-manager.ts` (1296)
5. `src/agents/validation-task-adapter.ts` (1266)

### 4.2 `any` 使用上位

1. `src/agents/domain-modeling-task-adapter.ts` (54)
2. `src/inference/core/solution-composer.ts` (35)
3. `src/agents/validation-task-adapter.ts` (33)
4. `src/services/container/podman-engine.ts` (32)
5. `src/services/container/docker-engine.ts` (32)

## 5. Phase 1着手前チェック

- [ ] `safe-remove` 対象が `.gitignore` で網羅されているか確認
- [ ] `needs-review` 対象の参照元を `rg` で抽出し、移動可否を判定
- [ ] ルート直下生成物の出力先変更方針を決定
- [ ] クリーンアップコマンドの標準運用（`clean:project`）を明文化

## 6. 補足

本ドキュメントは Phase 0 の固定スナップショットであり、Phase 1以降は「実施結果」として別ドキュメントに差分記録する。
