---
docRole: narrative
lastVerified: '2026-03-10'
---
# Verify Lite Lint Backlog 分析（Issue #1019）

> 🌍 Language / 言語: 日本語 (English TL;DR included inline)

## 現状サマリ
- 📊 合計 1,447 件
- 🛑 `no-unsafe-*` 系 686 件（47.4%）
- ⚠️ `no-explicit-any` 226 件（15.6%）
- 🔄 `no-unused-vars` 194 件（13.4%）
- ⏳ `require-await` 197 件（13.6%）
- ℹ️ 2026-02-23 時点の再集計値（`node scripts/quality/check-lint-summary.mjs`）
- 🛠 自動修正対象は 35 件（`no-unnecessary-type-assertion` が 31 件で最多）
- ✅ `src/inference/strategies/sequential-strategy.ts` は 107 件 → 0 件に改善（Issue #2214）

### ファイル別インパクト（抜粋）
| 主要ファイル | 代表的なルール | 指摘件数<sup>*</sup> |
| --- | --- | --- |
| `src/integration/runners/e2e-runner.ts` | require-await / no-unsafe-* | 110 |
| `src/integration/runners/api-runner.ts` | no-explicit-any / no-unsafe-* | 65 |
| `src/integration/hybrid-intent-system.ts` | no-explicit-any / no-unsafe-* | 56 |
| `src/self-improvement/phase4-code-generation.ts` | no-unsafe-* | 46 |
| `src/integration/hybrid-tdd-system.ts` | no-explicit-any / no-unsafe-* | 40 |

<sup>*</sup> 指摘件数は `reports/lint/verify-lite-lint-summary.json` の該当ファイル・ルールの合計値。

> English TL;DR: Unsafe typed interactions still dominate (~47%). `sequential-strategy` has been remediated (107 → 0), and remaining hotspots are concentrated in `integration` and `self-improvement` areas.

---

## Quality Gate 連携
- `node scripts/quality/check-lint-summary.mjs` を Quality Policy (development) の Lint gate から呼び出し、`config/verify-lite-lint-baseline.json` と差分比較して増加分のみを検出します。
- Quality gate は `maxErrors=0 / maxWarnings=0`（development 環境）運用のため、Verify Lite のベースラインを超える lint 指摘が追加されると即時に検知されます。
- サマリ JSON (`reports/lint/verify-lite-lint-summary.json`) は本スクリプトで再生成されるため、Verify Lite を事前に実行していない環境でもチェック可能です。

### Baseline 更新ルール
- baseline 更新は「総件数が減少」かつ「重点ルール（`no-explicit-any` / `no-unsafe-*`）が非増加」の場合のみ実施する。
- `unknown` ルール差分が増加した場合は baseline を更新せず、先に原因（ignore 設定・formatter差分等）を解消する。
- baseline 更新時は本ドキュメントに「対象PR」「前後件数」「未着手トップ3」を追記する。

## ルール別チェックリスト
各項目は **[ ]** → 未対応 / **[x]** → 解消済み で管理します。数字は現時点の残件数です（`reports/lint/verify-lite-lint-summary.json` から算出）。

### 1. `@typescript-eslint/no-unused-vars`（271）
- [ ] `src/inference/core/solution-composer.ts` (27)
- [ ] `src/inference/core/validation-orchestrator.ts` (17)
- [ ] `src/quality/quality-gate-runner.ts` (17)
- [ ] `src/utils/evidence-validator.ts` (17)
- [ ] `src/engines/sequential-inference-engine.ts` (13)
- [ ] `src/testing/visual-regression.ts` (12)
- [ ] `src/integration/runners/e2e-runner.ts` (11)
- [x] `src/inference/strategies/sequential-strategy.ts` (0, 2026-02-23)
- [ ] `src/integration/reporters/html-reporter.ts` (7)
- [ ] `src/self-improvement/phase5-verification-final.ts` (7)

### 2. `@typescript-eslint/require-await`（203）
- [ ] `src/integration/runners/e2e-runner.ts` (18)
- [ ] `src/inference/core/solution-composer.ts` (14)
- [ ] `src/inference/core/validation-orchestrator.ts` (9)
- [ ] `src/cegis/strategies/type-error-strategy.ts` (8)
- [x] `src/inference/strategies/sequential-strategy.ts` (0, 2026-02-23)
- [ ] `src/cegis/strategies/test-failure-strategy.ts` (6)
- [ ] `src/engines/sequential-inference-engine.ts` (6)
- [ ] `src/integration/hybrid-tdd-system.ts` (6)
- [ ] `src/integration/test-orchestrator.ts` (6)
- [ ] `src/utils/enhanced-state-manager.ts` (6)

### 3. `@typescript-eslint/no-explicit-any`（524）
- [ ] `src/inference/core/solution-composer.ts` (37)
- [x] `src/inference/strategies/sequential-strategy.ts` (0, 2026-02-23)
- [ ] `src/inference/core/validation-orchestrator.ts` (22)
- [ ] `src/server.ts` (22)
- [ ] `src/conformance/rule-engine.ts` (20)
- [ ] `src/integration/runners/api-runner.ts` (20)
- [ ] `src/integration/hybrid-intent-system.ts` (17)
- [ ] `src/integration/hybrid-tdd-system.ts` (17)
- [ ] `src/inference/strategies/parallel-strategy.ts` (16)
- [ ] `src/engines/sequential-inference-engine.ts` (15)

### 4. `no-unsafe-*` クラスター（計 1,202）
#### 4-1. `@typescript-eslint/no-unsafe-assignment`（350）
- [x] `src/inference/strategies/sequential-strategy.ts` (0, 2026-02-23)
- [ ] `src/integration/runners/e2e-runner.ts` (19)
- [ ] `src/conformance/monitors/data-validation-monitor.ts` (18)
- [ ] `src/inference/core/solution-composer.ts` (17)
- [ ] `src/inference/strategies/parallel-strategy.ts` (17)
- [ ] `src/integration/circuit-breaker-integration.ts` (16)
- [ ] `src/utils/persona-manager.ts` (15)
- [ ] `src/security/sbom-generator.ts` (14)
- [ ] `src/integration/runners/api-runner.ts` (13)
- [ ] `src/server.ts` (13)

#### 4-2. `@typescript-eslint/no-unsafe-member-access`（597）
- [ ] `src/codegen/deterministic-generator.ts` (36)
- [ ] `src/integration/runners/e2e-runner.ts` (28)
- [ ] `src/security/sbom-generator.ts` (27)
- [ ] `src/self-improvement/phase4-code-generation.ts` (27)
- [ ] `src/integration/runners/api-runner.ts` (24)
- [ ] `src/server.ts` (23)
- [x] `src/inference/strategies/sequential-strategy.ts` (0, 2026-02-23)
- [ ] `src/testing/playwright-integration.ts` (20)
- [ ] `src/optimization/monitoring/demo.ts` (19)
- [ ] `src/optimization/parallel/parallel-optimizer.ts` (18)

#### 4-3. `@typescript-eslint/no-unsafe-argument`（143）
- [ ] `src/integration/runners/e2e-runner.ts` (20)
- [x] `src/inference/strategies/sequential-strategy.ts` (0, 2026-02-23)
- [ ] `src/mcp-server/intent-server.ts` (9)
- [ ] `src/integration/hybrid-intent-system.ts` (8)
- [ ] `src/optimization/parallel/parallel-optimizer.ts` (8)
- [ ] `src/self-improvement/phase4-code-generation.ts` (8)
- [ ] `src/cegis/strategies/contract-violation-strategy.ts` (7)
- [ ] `src/conformance/monitors/data-validation-monitor.ts` (7)
- [ ] `src/integration/runners/api-runner.ts` (7)
- [ ] `src/optimization/parallel/index.ts` (7)

#### 4-4. `@typescript-eslint/no-unsafe-return`（38）
- [ ] `src/integration/circuit-breaker-integration.ts` (7)
- [ ] `src/codegen/drift-detector.ts` (3)
- [ ] `src/codegen/deterministic-generator.ts` (2)
- [ ] `src/conformance/rule-engine.ts` (2)
- [ ] `src/testing/visual-regression.ts` (2)
- [ ] `src/utils/phase-state-manager.ts` (2)
- [ ] `src/utils/quality-policy-loader.ts` (2)
- [ ] `src/conformance/monitors/api-contract-monitor.ts` (1)
- [ ] `src/conformance/monitors/data-validation-monitor.ts` (1)
- [ ] `src/generators/ui-scaffold-generator.ts` (1)

---

## `--fix` 対応可能な指摘（42）
- Stage 1 (`@typescript-eslint/no-unnecessary-type-assertion` / `prefer-const` / unused disable) は完了したが、最新集計では `no-unnecessary-type-assertion` を中心に 42 件の fixable が再発。Stage 2 の対象ファイルへ再度 `--fix` バッチを適用する必要がある。

---

## 段階的な移行ロードマップ案
1. **Stage 0 — Baseline 整理（今）**  
   - 本ドキュメントでカテゴリ＆ファイル別の棚卸しを確定。  
   - `scripts/quality/check-lint-summary.mjs` で `reports/lint/verify-lite-lint-summary.json` を自動再生成し、`config/verify-lite-lint-baseline.json` と突き合わせる。
2. **Stage 1 — `--fix` バッチ適用（完了）**  
   - `no-unnecessary-type-assertion` / `prefer-const` / unused disable を解消し、backlog を 2,202 件（fixable 0）まで削減。  
   - `config/verify-lite-lint-baseline.json` を最新サマリに合わせて更新済み。
3. **Stage 2 — 優先 5 ファイルの Unsafe & any 解消**  
   - `integration/runners/e2e-runner.ts`, `inference/strategies/sequential-strategy.ts`, `inference/core/solution-composer.ts`, `integration/runners/api-runner.ts`, `server.ts` を対象に型付けとユーティリティ抽出を実施（`sequential-strategy.ts` は 2026-02-23 に完了）。  
   - 残件の Unsafe 系を継続的に削減し、`no-explicit-any` はドメイン型を定義した DTO で置換。
4. **Stage 3 — Verify Lite Lint の段階的強制**  
   - PR ラベル (`lint-blocking`) で opt-in → `main` で警告 → CI で `VERIFY_LITE_ENFORCE_LINT=1` に引き上げ。  
   - 成果は `docs/quality/verify-lite-lint-backlog.md` に更新履歴を追記。

---

## 自動化スクリプト
Verify Lite lint の集計は以下の手順で再現できる。

```bash
node scripts/quality/check-lint-summary.mjs
```

`check-lint-summary.mjs` は ESLint を JSON モードで実行し、ルール・ファイル別件数と fixable 集計を算出して `reports/lint/verify-lite-lint-summary.json` を更新する。同時に `config/verify-lite-lint-baseline.json` と比較して差分を出力するため、本ドキュメント更新や baseline 比較を一本化できる。

---

## 次のステップ（Issue #1019 対応観点）
1. Stage 2: `integration/runners/e2e-runner.ts` / `inference/core/solution-composer.ts` / `integration/runners/api-runner.ts` / `server.ts` の Unsafe/any 改修（`sequential-strategy.ts` は完了済み）  
2. Stage 2 完了後に lint サマリを Step Summary / CI に連携する運用案を整理  
3. Verify Lite lint を警告モードで CI に組み込み、効果測定  
4. 本ドキュメントに PBI／PR 単位で進捗を追記し、Issue コメントと連動させる

> English TL;DR: With runtime middleware stabilized, focus on reducing the remaining five hotspots (e2e-runner, sequential-strategy, solution-composer, api-runner, server) and clear the 42 newly surfaced fixable assertions before raising lint enforcement in CI.
