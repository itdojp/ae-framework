# Verify Lite Lint Backlog 分析（Issue #1019）

> 🌍 Language / 言語: 日本語 (English TL;DR included inline)

## 現状サマリ
- 📊 合計 2,101 件（前回 2,202 件から **-101**）
- 🛑 `no-unsafe-*` 系 1,078 件（51.3%）
- ⚠️ `no-explicit-any` 469 件（22.3%）
- 🔄 `no-unused-vars` 264 件（12.6%）
- ⏳ `require-await` 195 件（9.3%）
- 🛠 自動修正対象は 0 件（Stage 1 `--fix` 残タスクの `src/server.ts` を解消済み）

### ファイル別インパクト（抜粋）
| 主要ファイル | 代表的なルール | 指摘件数<sup>*</sup> |
| --- | --- | --- |
| `src/integration/runners/e2e-runner.ts` | require-await / no-unsafe-* | 117 |
| `src/inference/core/solution-composer.ts` | no-unused-vars / require-await / no-explicit-any | 97 |
| `src/integration/runners/api-runner.ts` | no-explicit-any / no-unsafe-* | 79 |
| `src/inference/core/validation-orchestrator.ts` | no-unused-vars / no-explicit-any | 73 |
| `src/codegen/deterministic-generator.ts` | no-unsafe-member-access / require-await | 65 |

<sup>*</sup> 指摘件数は `reports/lint/verify-lite-lint-summary.json` の該当ファイル・ルールの合計値。

> English TL;DR: Unsafe typed interactions still dominate (~51%), followed by `any` usage (~22%). Five files (`e2e-runner`, `solution-composer`, `integration/runners/api-runner`, `validation-orchestrator`, `codegen/deterministic-generator`) now concentrate ~19% of the backlog and remain the primary remediation targets.

---

## ルール別チェックリスト
各項目は **[ ]** → 未対応 / **[x]** → 解消済み で管理します。数字は現時点の残件数です（`reports/lint/verify-lite-lint-summary.json` から算出）。

### 1. `@typescript-eslint/no-unused-vars`（264）
- [ ] `src/inference/core/solution-composer.ts` (27)
- [ ] `src/inference/core/validation-orchestrator.ts` (17)
- [ ] `src/quality/quality-gate-runner.ts` (17)
- [ ] `src/utils/evidence-validator.ts` (17)
- [ ] `src/engines/sequential-inference-engine.ts` (13)
- [ ] `src/testing/visual-regression.ts` (12)
- [ ] `src/integration/runners/e2e-runner.ts` (11)
- [ ] `src/integration/reporters/html-reporter.ts` (7)
- [ ] `src/self-improvement/phase5-verification-final.ts` (7)
- [ ] `src/self-improvement/codebase-analysis.ts` (6)

### 2. `@typescript-eslint/require-await`（195）
- [ ] `src/integration/runners/e2e-runner.ts` (18)
- [ ] `src/inference/core/solution-composer.ts` (14)
- [ ] `src/inference/core/validation-orchestrator.ts` (9)
- [ ] `src/cegis/strategies/type-error-strategy.ts` (8)
- [ ] `src/cegis/strategies/test-failure-strategy.ts` (6)
- [ ] `src/engines/sequential-inference-engine.ts` (6)
- [ ] `src/integration/hybrid-tdd-system.ts` (6)
- [ ] `src/integration/test-orchestrator.ts` (6)
- [ ] `src/utils/enhanced-state-manager.ts` (6)
- [ ] `src/codegen/deterministic-generator.ts` (5)

### 3. `@typescript-eslint/no-explicit-any`（469）
- [ ] `src/inference/core/solution-composer.ts` (37)
- [ ] `src/inference/core/validation-orchestrator.ts` (22)
- [ ] `src/conformance/rule-engine.ts` (20)
- [ ] `src/integration/runners/api-runner.ts` (20)
- [ ] `src/integration/circuit-breaker-integration.ts` (17)
- [ ] `src/integration/hybrid-intent-system.ts` (17)
- [ ] `src/integration/hybrid-tdd-system.ts` (17)
- [ ] `src/inference/strategies/parallel-strategy.ts` (16)
- [ ] `src/engines/sequential-inference-engine.ts` (15)

### 4. `no-unsafe-*` クラスター（計 1,078）
#### 4-1. `@typescript-eslint/no-unsafe-assignment`（304）
- [ ] `src/integration/runners/e2e-runner.ts` (19)
- [ ] `src/conformance/monitors/data-validation-monitor.ts` (18)
- [ ] `src/inference/core/solution-composer.ts` (17)
- [ ] `src/integration/circuit-breaker-integration.ts` (16)
- [ ] `src/utils/persona-manager.ts` (15)
- [ ] `src/security/sbom-generator.ts` (14)
- [ ] `src/integration/runners/api-runner.ts` (13)
- [ ] `src/inference/strategies/parallel-strategy.ts` (12)
- [ ] `src/integration/hybrid-tdd-system.ts` (11)
- [ ] `src/optimization/parallel/parallel-optimizer.ts` (11)

#### 4-2. `@typescript-eslint/no-unsafe-member-access`（544）
- [ ] `src/codegen/deterministic-generator.ts` (36)
- [ ] `src/integration/runners/e2e-runner.ts` (28)
- [ ] `src/security/sbom-generator.ts` (27)
- [ ] `src/self-improvement/phase4-code-generation.ts` (27)
- [ ] `src/integration/runners/api-runner.ts` (24)
- [ ] `src/testing/playwright-integration.ts` (20)
- [ ] `src/optimization/monitoring/demo.ts` (19)
- [ ] `src/optimization/parallel/parallel-optimizer.ts` (18)
- [ ] `src/utils/persona-manager.ts` (17)
- [ ] `src/integration/hybrid-intent-system.ts` (16)

#### 4-3. `@typescript-eslint/no-unsafe-argument`（123）
- [ ] `src/integration/runners/e2e-runner.ts` (20)
- [ ] `src/mcp-server/intent-server.ts` (9)
- [ ] `src/integration/hybrid-intent-system.ts` (8)
- [ ] `src/optimization/parallel/parallel-optimizer.ts` (8)
- [ ] `src/self-improvement/phase4-code-generation.ts` (8)
- [ ] `src/cegis/strategies/contract-violation-strategy.ts` (7)
- [ ] `src/conformance/monitors/data-validation-monitor.ts` (7)
- [ ] `src/integration/runners/api-runner.ts` (7)
- [ ] `src/optimization/parallel/index.ts` (7)
- [ ] `src/security/sbom-generator.ts` (6)

#### 4-4. `@typescript-eslint/no-unsafe-return`（36）
- [ ] `src/integration/circuit-breaker-integration.ts` (7)
- [ ] `src/codegen/drift-detector.ts` (3)
- [ ] `src/codegen/deterministic-generator.ts` (2)
- [ ] `src/conformance/rule-engine.ts` (2)
- [ ] `src/testing/visual-regression.ts` (2)
- [ ] `src/utils/quality-policy-loader.ts` (2)
- [ ] `src/conformance/monitors/api-contract-monitor.ts` (1)
- [ ] `src/conformance/monitors/data-validation-monitor.ts` (1)
- [ ] `src/generators/ui-scaffold-generator.ts` (1)
- [ ] `src/inference/core/validation-orchestrator.ts` (1)

---

## `--fix` 対応可能な指摘（10）
- Stage 1 (`@typescript-eslint/no-unnecessary-type-assertion` / `prefer-const` / unused disable) は完了。残タスクは Stage 2 以降に集約。

---

## 段階的な移行ロードマップ案
1. **Stage 0 — Baseline 整理（今）**  
   - 本ドキュメントでカテゴリ＆ファイル別の棚卸しを確定。  
   - `scripts/ci/analyze-lint-backlog.mjs` により `reports/lint/verify-lite-lint-summary.json` を自動生成。
2. **Stage 1 — `--fix` バッチ適用（完了）**  
   - `no-unnecessary-type-assertion` / `prefer-const` / unused disable を解消し、backlog を 2,202 件（fixable 0）まで削減。  
   - `config/verify-lite-lint-baseline.json` を最新サマリに合わせて更新済み。
3. **Stage 2 — 優先 5 ファイルの Unsafe & any 解消**  
   - `integration/runners/e2e-runner.ts`, `inference/core/solution-composer.ts`, `integration/runners/api-runner.ts`, `inference/core/validation-orchestrator.ts`, `codegen/deterministic-generator.ts` を対象に型付けとユーティリティ抽出を実施。  
   - ここで Unsafe 系を 25% 減らし、`no-explicit-any` はドメイン型を定義した DTO で置換。
4. **Stage 3 — Verify Lite Lint の段階的強制**  
   - PR ラベル (`lint-blocking`) で opt-in → `main` で警告 → CI で `VERIFY_LITE_ENFORCE_LINT=1` に引き上げ。  
   - 成果は `docs/quality/verify-lite-lint-backlog.md` に更新履歴を追記。

---

## 自動化スクリプト
Verify Lite lint の集計は以下の手順で再現できる。

```bash
pnpm exec eslint --ext .ts,.tsx,.js,.mjs --format json --output-file temp-reports/verify-lite-lint.json
node scripts/ci/analyze-lint-backlog.mjs --input temp-reports/verify-lite-lint.json --output reports/lint/verify-lite-lint-summary.json
```

`analyze-lint-backlog.mjs` はルール単位の件数、主要ファイル、fixable 集計を自動算出するため、本ドキュメント更新や baseline 比較を高速化できる。

---

## 次のステップ（Issue #1019 対応観点）
1. Stage 2: `conformance-guards.ts` / `solution-composer.ts` / `integration` 系ファイルの Unsafe/any 改修  
2. Stage 2 完了後に lint サマリを Step Summary / CI に連携する運用案を整理  
3. Verify Lite lint を警告モードで CI に組み込み、効果測定  
4. 本ドキュメントに PBI／PR 単位で進捗を追記し、Issue コメントと連動させる

> English TL;DR: Start with the fixable assertions, then harden the five core files, finally promote lint enforcement in CI once Unsafe + `any` hotspots have been reduced by ~25%.
