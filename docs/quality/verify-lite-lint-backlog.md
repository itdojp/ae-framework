# Verify Lite Lint Backlog 分析（Issue #1019）

> 🌍 Language / 言語: 日本語 (English TL;DR included inline)

## 現状サマリ
- 📊 合計 2,668 件（baseline 2,618 から +50）
- 🛑 `no-unsafe-*` 系 1,394 件（52.3%）
- ⚠️ `no-explicit-any` 620 件（23.2%）
- 🔄 `no-unused-vars` 274 件（10.3%）
- ⏳ `require-await` 205 件（7.7%）
- 🛠 `--fix` で自動修正可能な指摘は 46 件（主に `no-unnecessary-type-assertion`）

### ファイル別インパクト（抜粋）
| 主要ファイル | 代表的なルール | 指摘件数<sup>*</sup> |
| --- | --- | --- |
| `src/runtime/runtime-middleware.ts` | no-explicit-any / no-unsafe-* | 154 |
| `src/inference/core/solution-composer.ts` | no-unused-vars / require-await / no-explicit-any | 81 |
| `src/inference/strategies/sequential-strategy.ts` | no-explicit-any / no-unsafe-* | 98 |
| `src/integration/runners/e2e-runner.ts` | require-await / no-unsafe-* | 79 |
| `src/runtime/conformance-guards.ts` | no-explicit-any / no-unsafe-* | 89 |

<sup>*</sup> 指摘件数は `reports/lint/verify-lite-lint-summary.json` の該当ファイル・ルールの合計値。

> English TL;DR: Unsafe typed interactions dominate (52%), followed by `any` usage (23%). Five files (`runtime-middleware`, `solution-composer`, `sequential-strategy`, `e2e-runner`, `conformance-guards`) account for ~20% of the backlog and should anchor the first remediation sprint.

---

## ルール別チェックリスト
各項目は **[ ]** → 未対応 / **[x]** → 解消済み で管理します。数字は現時点の残件数です（`reports/lint/verify-lite-lint-summary.json` から算出）。

### 1. `@typescript-eslint/no-unused-vars`（274）
- [ ] `src/inference/core/solution-composer.ts` (27)
- [ ] `src/inference/core/validation-orchestrator.ts` (17)
- [ ] `src/quality/quality-gate-runner.ts` (17)
- [ ] `src/utils/evidence-validator.ts` (17)
- [ ] `src/engines/sequential-inference-engine.ts` (13)
- [ ] `src/testing/visual-regression.ts` (12)
- [ ] `src/integration/runners/e2e-runner.ts` (11)
- [ ] `src/inference/strategies/sequential-strategy.ts` (7)
- [ ] `src/integration/reporters/html-reporter.ts` (7)
- [ ] `src/self-improvement/phase5-verification-final.ts` (7)

### 2. `@typescript-eslint/require-await`（205）
- [ ] `src/integration/runners/e2e-runner.ts` (18)
- [ ] `src/inference/core/solution-composer.ts` (14)
- [ ] `src/inference/core/validation-orchestrator.ts` (9)
- [ ] `src/cegis/strategies/type-error-strategy.ts` (8)
- [ ] `src/inference/strategies/sequential-strategy.ts` (8)
- [ ] `src/cegis/strategies/test-failure-strategy.ts` (6)
- [ ] `src/engines/sequential-inference-engine.ts` (6)
- [ ] `src/integration/hybrid-tdd-system.ts` (6)
- [ ] `src/integration/test-orchestrator.ts` (6)
- [ ] `src/utils/enhanced-state-manager.ts` (6)

### 3. `@typescript-eslint/no-explicit-any`（620）
- [ ] `src/runtime/runtime-middleware.ts` (53)
- [ ] `src/inference/core/solution-composer.ts` (37)
- [ ] `src/inference/strategies/sequential-strategy.ts` (31)
- [ ] `src/runtime/conformance-guards.ts` (31)
- [ ] `src/inference/core/validation-orchestrator.ts` (22)
- [ ] `src/server.ts` (22)
- [ ] `src/conformance/rule-engine.ts` (20)
- [ ] `src/integration/runners/api-runner.ts` (20)
- [ ] `src/integration/circuit-breaker-integration.ts` (17)
- [ ] `src/integration/hybrid-intent-system.ts` (17)

### 4. `no-unsafe-*` クラスター（計 1,394）
#### 4-1. `@typescript-eslint/no-unsafe-assignment`
- [ ] `src/runtime/runtime-middleware.ts` (43)
- [ ] `src/inference/strategies/sequential-strategy.ts` (24)
- [ ] `src/integration/runners/e2e-runner.ts` (19)
- [ ] `src/runtime/conformance-guards.ts` (19)
- [ ] `src/conformance/monitors/data-validation-monitor.ts` (18)
- [ ] `src/inference/core/solution-composer.ts` (17)
- [ ] `src/inference/strategies/parallel-strategy.ts` (17)
- [ ] `src/integration/circuit-breaker-integration.ts` (16)
- [ ] `src/utils/persona-manager.ts` (15)
- [ ] `src/security/sbom-generator.ts` (14)

#### 4-2. `@typescript-eslint/no-unsafe-member-access`
- [ ] `src/runtime/runtime-middleware.ts` (45)
- [ ] `src/codegen/deterministic-generator.ts` (36)
- [ ] `src/runtime/conformance-guards.ts` (29)
- [ ] `src/integration/runners/e2e-runner.ts` (28)
- [ ] `src/security/sbom-generator.ts` (27)
- [ ] `src/self-improvement/phase4-code-generation.ts` (27)
- [ ] `src/integration/runners/api-runner.ts` (24)
- [ ] `src/server.ts` (23)
- [ ] `src/inference/strategies/sequential-strategy.ts` (22)
- [ ] `src/testing/playwright-integration.ts` (20)

#### 4-3. `@typescript-eslint/no-unsafe-argument`
- [ ] `src/integration/runners/e2e-runner.ts` (20)
- [ ] `src/inference/strategies/sequential-strategy.ts` (11)
- [ ] `src/mcp-server/intent-server.ts` (9)
- [ ] `src/integration/hybrid-intent-system.ts` (8)
- [ ] `src/optimization/parallel/parallel-optimizer.ts` (8)
- [ ] `src/self-improvement/phase4-code-generation.ts` (8)
- [ ] `src/cegis/strategies/contract-violation-strategy.ts` (7)
- [ ] `src/conformance/monitors/data-validation-monitor.ts` (7)
- [ ] `src/integration/runners/api-runner.ts` (7)
- [ ] `src/optimization/parallel/index.ts` (7)

#### 4-4. `@typescript-eslint/no-unsafe-return`
- [ ] `src/runtime/runtime-middleware.ts` (13)
- [ ] `src/integration/circuit-breaker-integration.ts` (7)
- [ ] `src/runtime/conformance-guards.ts` (5)
- [ ] `src/codegen/drift-detector.ts` (3)
- [ ] `src/codegen/deterministic-generator.ts` (2)
- [ ] `src/conformance/rule-engine.ts` (2)
- [ ] `src/testing/visual-regression.ts` (2)
- [ ] `src/utils/circuit-breaker.ts` (2)
- [ ] `src/utils/phase-state-manager.ts` (2)
- [ ] `src/utils/quality-policy-loader.ts` (2)

---

## `--fix` 対応可能な指摘（46）
- 43 件: `@typescript-eslint/no-unnecessary-type-assertion`
  - 主なファイル: `src/server.ts` (10), `src/telemetry/enhanced-telemetry.ts` (6), `src/utils/enhanced-state-manager.ts` (6), `src/mcp-server/code-generation-server.ts` (4), `src/mcp-server/test-generation-server.ts` (4)
- 2 件: `prefer-const`
- 1 件: ルール ID なし（個別確認が必要）

> ✅ これらは `pnpm exec eslint <targets> --fix` で安全に解消できるため、フェーズBの最初の PR 候補。

---

## 段階的な移行ロードマップ案
1. **Stage 0 — Baseline 整理（今）**  
   - 本ドキュメントでカテゴリ＆ファイル別の棚卸しを確定。  
   - `reports/lint/verify-lite-lint-summary.json` を毎スプリント更新するスクリプト化（後述）。
2. **Stage 1 — `--fix` バッチ適用**  
   - `no-unnecessary-type-assertion` と `prefer-const` を一括修正。  
   - `config/verify-lite-lint-baseline.json` を更新し、delta を 2600 → 2550 付近まで圧縮。
3. **Stage 2 — 優先 5 ファイルの Unsafe & any 解消**  
   - `runtime-middleware`, `solution-composer`, `sequential-strategy`, `e2e-runner`, `conformance-guards` を対象に型付けとユーティリティ抽出を実施。  
   - ここで Unsafe 系を 25% 減らし、`no-explicit-any` はドメイン型を定義した DTO で置換。
4. **Stage 3 — Verify Lite Lint の段階的強制**  
   - PR ラベル (`lint-blocking`) で opt-in → `main` で警告 → CI で `VERIFY_LITE_ENFORCE_LINT=1` に引き上げ。  
   - 成果は `docs/quality/verify-lite-lint-backlog.md` に更新履歴を追記。

---

## 自動化スクリプト（案）
追跡のために以下を追加予定です（別 PR）。

```bash
pnpm exec eslint . --format json --output-file temp-reports/verify-lite-lint.json
node scripts/ci/analyze-lint-backlog.mjs --input temp-reports/verify-lite-lint.json --output reports/lint/verify-lite-lint-summary.json
```

`analyze-lint-backlog.mjs` はルール単位の件数、上位ファイル、fixable 件数を出力し、本ドキュメントと同期を取りやすくします。

---

## 次のステップ（Issue #1019 対応観点）
1. `--fix` 対応 PR のドラフト（Stage 1）  
2. 優先 5 ファイルの Unsafe/any 改修着手（Stage 2）  
3. Verify Lite lint を警告モードで CI に組み込み、効果測定  
4. 本ドキュメントに PBI／PR 単位で進捗を追記し、Issue コメントと連動させる

> English TL;DR: Start with the fixable assertions, then harden the five core files, finally promote lint enforcement in CI once Unsafe + `any` hotspots have been reduced by ~25%.
