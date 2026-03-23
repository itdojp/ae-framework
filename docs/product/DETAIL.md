---
docRole: derived
canonicalSource:
- docs/architecture/CURRENT-SYSTEM-OVERVIEW.md
- docs/quality/formal-runbook.md
lastVerified: '2026-03-23'
---
# ae-framework 詳細説明資料

> Language / 言語: English | 日本語

---

## English

### 1. Scope and Assumptions
`ae-framework` is an operating foundation for specification, verification, and CI in agent-assisted SDLC. The product is centered on four layers:
- specification and verification assets, including specs, formal tooling, and tests
- execution tooling such as CLI entry points and automation scripts
- operational integration through CI quality gates and workflow orchestration
- artifacts and reports for both machine and human consumers

For environment prerequisites, see `docs/product/OVERVIEW.md`.

### 2. Logical Architecture
#### 2.1 Layers
1. Operations layer
   - GitHub Actions workflows under `.github/workflows/*`
   - PR labels, comments, and lightweight gate operation
2. Execution layer
   - CLI entry points from `src/cli/*` and `package.json` `bin`
   - automation scripts under `scripts/*`
3. Specification and verification layer
   - specifications under `spec/`
   - formal tooling under `scripts/formal/*`
   - tests under `tests/*` and `spec/bdd/*`
4. Artifact layer
   - machine-readable outputs under `artifacts/*`
   - human-readable reports under `reports/*`

#### 2.2 Major Components
- CLI surface: `ae`, `ae-framework`, `ae-phase`, `ae-approve`, `ae-slash`, `ae-ui`, `ae-sbom`, `ae-resilience`, `ae-benchmark`, `ae-server`
- Main subcommands registered by `src/cli/index.ts`, including `spec`, `state-machine`, `codegen`, `fix`, `quality`, `qa`, `conformance`, `integration`, and progress views
- Legacy compatibility shims remain in `src/cli.ts` and `src/runner/main.ts`; new user-facing commands are not added there

#### 2.3 CLI and entrypoint detail
- Source entrypoints behind the binaries declared in `package.json bin` (built into `dist/src/cli/*.js` at runtime):
  - `ae`, `ae-framework` -> `src/cli/index.ts`
  - `ae-phase` -> `src/cli/phase-cli.ts`
  - `ae-approve` -> `src/cli/approval-cli.ts`
  - `ae-slash` -> `src/cli/slash-cli.ts`
  - `ae-ui` -> `src/cli/ae-ui-alias.ts`
  - `ae-sbom` -> `src/cli/sbom-cli.ts`
  - `ae-resilience` -> `src/cli/resilience-cli.ts`
  - `ae-benchmark` -> `src/cli/benchmark-cli.ts`
  - `ae-server` -> `src/cli/server-runner.ts`
- For the exact runtime mapping, consult `package.json` `bin` entries and the built `dist/src/cli/*.js` outputs.
- Representative subcommands from `src/cli/index.ts`:
  - `spec`
  - `state-machine`
  - `codegen`
  - `fix`
  - `enhanced-state`
  - `circuit-breaker`
  - `security`
  - `entry`
  - `help`
  - `setup`
  - `quality`
  - `qa`
  - `conformance`
  - `integration`
  - `resilience`
  - `sbom`
  - `status` / `board`

### 3. Specification and Verification
- Registry and contract references live under `spec/` and `docs/spec/registry.md`
- Formal verification is documented in `docs/quality/formal-runbook.md` and implemented through `scripts/formal/*`
- Core spec lifecycle commands remain `spec:compile`, `spec:lint`, and `spec:validate`

### 4. Repository Structure

| Directory | Responsibility |
| --- | --- |
| `src/` | Core implementation, CLI entrypoints, and MCP/server logic |
| `scripts/` | CI, quality, security, and verification automation |
| `docs/` | Reference, runbook, and onboarding documentation |
| `spec/` | Specification registry and definition inputs |
| `tests/` | Unit, integration, property, and resilience-oriented tests |
| `packages/` | Subpackages such as compilers and support utilities |
| `templates/` | Spec, CI, and quality templates |
| `artifacts/`, `reports/` | Machine-readable evidence and human-readable reports |
| `configs/` | TypeScript, test, and CI-related configuration |

### 5. Primary Flows
#### 5.1 Local verification path
1. Install dependencies with `pnpm install`
2. Run the minimum baseline with `pnpm run lint` and `pnpm run test:fast`
3. Run `pnpm run verify:formal` when formal evidence is needed

#### 5.2 CI path
1. Open the PR
2. Pass `verify-lite`, `policy-gate`, and `gate` as the lightweight baseline
3. Trigger `formal-verify` with the `run-formal` label or `workflow_dispatch` when needed
4. Add `enforce-formal` only when Apalache `ran/ok` must become blocking

#### 5.3 Specification validation path
1. Register or update specs under `spec/`
2. Run `spec:validate` for syntax and contract validation
3. Use formal verification to surface counterexamples and inconsistencies

### 6. Test Structure
The repository separates unit, integration, property, BDD, MBT, and resilience-oriented tests. Representative areas include:
- `tests/property/`
- `tests/integration/`
- `spec/bdd/`

### 7. CI and Quality Gates
Primary workflows are consolidated under `.github/workflows/`.
- Current main PR baseline uses the required check contexts `verify-lite`, `policy-gate`, and `gate`
- The corresponding workflows are `verify-lite.yml`, `policy-gate.yml`, and `copilot-review-gate.yml`
- Formal workflows: `formal-verify.yml`, `formal-aggregate.yml`
- Security workflows: `security.yml`, `sbom-generation.yml`
- Additional CI lanes: `ci-fast.yml`, `ci-extended.yml`, `pr-verify.yml`

### 8. Formal Verification Stack
`scripts/formal/*` operates the formal toolchain in non-blocking mode and aggregates outputs under `artifacts/hermetic-reports/formal/`.
- Individual runners include conformance, Alloy, TLA, SMT, Kani, SPIN, CSP, Lean, and Apalache
- Unified execution: `pnpm run verify:formal`
- Aggregate reporting: `pnpm run formal:summary`
- CSP integration prefers `cspx` when available and persists backend/status/resultStatus/exitCode details for PR-facing aggregation

### 9. Artifacts and Traceability
- CI outputs are retained under `artifacts/` and `reports/`
- CI comments and summary rendering consume the aggregated evidence
- Formal evidence is aggregated primarily into `artifacts/hermetic-reports/formal/summary.json`
- CSP-specific details are retained in `artifacts/hermetic-reports/formal/csp-summary.json` and `artifacts/hermetic-reports/formal/cspx-result.json`
- Traceability design is documented in `docs/verify/TRACEABILITY-GUIDE.md`

### 10. Security and Compliance
- Security validation workflows: `security.yml`, `sbom-generation.yml`
- The operating model assumes SBOM generation and dependency auditing can be enabled when repository policy requires them

### 11. Constraints and References
- `ae-framework` provides the operating model for CI/CD and evidence, not managed operations itself
- Agent runtimes remain external integrations
- `pnpm run verify:lite` depends on the JS/TS toolchain through `scripts/ci/run-verify-lite-local.sh`
- For non-JS projects, specification-centric features such as `verify:formal` and `verify:conformance` can be adopted first, with language-specific gates connected separately later

Related documents:
- `docs/product/OVERVIEW.md`
- `docs/product/USER-MANUAL.md`
- `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- `docs/README.md`

---

## 日本語

## 1. スコープと前提
ae-framework は、エージェント協調型SDLCを支える「仕様・検証・CI運用」の基盤です。プロダクトの中心は以下です。

- 仕様の登録と検証（Spec & Verification Kit）
- CI品質ゲート（verify-lite、coverage、securityなど）
- CLIとスクリプトによる運用自動化

前提条件は `docs/product/OVERVIEW.md` を参照してください。

## 2. 全体アーキテクチャ（論理）

### 2.1 レイヤ構成
1. **運用レイヤ**  
   - GitHub Actions: `.github/workflows/*`
   - PRコメントやラベル運用（verify-lite 等）
2. **実行レイヤ**  
   - CLI: `src/cli/*` と `package.json bin`
   - スクリプト: `scripts/*`
3. **仕様・検証レイヤ**  
   - 仕様: `spec/`, `docs/spec/registry.md`
   - 形式検証: `scripts/formal/*`
   - テスト: `tests/*`, `spec/bdd/*`
4. **成果物レイヤ**  
   - アーティファクト: `artifacts/*`
   - レポート: `reports/*`

### 2.2 主要コンポーネント

#### CLI
`package.json` の `bin` により以下のCLIが定義されています。

- `ae`, `ae-framework`: メインCLI（`src/cli/index.ts`）
- `ae-phase`: フェーズ関連CLI（`src/cli/phase-cli.ts`）
- `ae-approve`: 承認フロー用CLI（`src/cli/approval-cli.ts`）
- `ae-slash`: Slash コマンド関連CLI（`src/cli/slash-cli.ts`）
- `ae-ui`: UI向けエイリアス（`src/cli/ae-ui-alias.ts`）
- `ae-sbom`: SBOM関連CLI（`src/cli/sbom-cli.ts`）
- `ae-resilience`: レジリエンス機能CLI（`src/cli/resilience-cli.ts`）
- `ae-benchmark`: ベンチマークCLI（`src/cli/benchmark-cli.ts`）
- `ae-server`: サーバー起動（`src/cli/server-runner.ts`）

上記とは別に、メインCLI（`src/cli/index.ts`）は **サブコマンド** を登録しており、開発時は `pnpm run ae-framework -- <command>` 形式で呼び出せます。
`src/cli.ts` と `src/runner/main.ts` は legacy compatibility shim であり、主に `benchmark-report/v1` など旧導線互換のために残しています。新規の user-facing command はここへ追加しません。

代表的なサブコマンド（定義元）は以下です。

- `spec`（`src/cli/spec-cli.ts`）
- `state-machine`（`src/cli/state-machine-cli.ts`）
- `codegen`（`src/cli/codegen-cli.ts`）
- `fix`（CEGIS自動修復、`src/cli/cegis-cli.ts`）
- `enhanced-state`（`src/cli/enhanced-state-cli.ts`）
- `circuit-breaker`（`src/cli/circuit-breaker-cli.ts`）
- `security`（`src/cli/security-cli.ts`）
- `entry`（`src/cli/entry-runner-cli.ts`）
- `help`（`src/cli/help-cli.ts`。`pnpm run help` と同等の出力を目標）
- `setup`（`src/cli/setup-cli.ts`）
- `quality`（`src/cli/quality-cli.ts`）
- `qa`（`src/cli/qa-cli.ts`）
- `conformance`（`src/cli/conformance-cli.ts`）
- `integration`（`src/cli/integration-cli.ts`）
- `resilience`（`src/cli/resilience-cli.ts`）
- `sbom`（`src/cli/sbom-cli.ts`）
- `status` / `board`（`src/cli/progress-cli.ts`。`pnpm run progress:summary` の結果を参照）

#### 仕様と検証
- 仕様レジストリ: `docs/spec/registry.md`
- フォーマル検証: `docs/quality/formal-runbook.md`, `scripts/formal/*`
- 仕様コンパイル/検証: `spec:compile`, `spec:lint`, `spec:validate`（`package.json scripts`）

#### テスト体系
- ユニット、統合、プロパティテスト、BDD、MBTを分離した構成
- 例: `tests/property/`, `tests/integration/`, `spec/bdd/`

#### CIと品質ゲート
主要ワークフローは `.github/workflows/` に集約されています。

- current main の代表的な PR ゲート: `verify-lite.yml`, `policy-gate.yml`, `copilot-review-gate.yml`（required context は `gate`）
- 形式検証: `formal-verify.yml`, `formal-aggregate.yml`
- セキュリティ: `security.yml`, `sbom-generation.yml`
- その他: `ci-fast.yml`, `ci-extended.yml`, `pr-verify.yml`

### 2.3 形式検証スタック（拡張後）
`scripts/formal/*` は全ツールを non-blocking で統一運用し、`artifacts/hermetic-reports/formal/` に summary を出力します。

- ランナー: `verify:conformance`, `verify:alloy`, `verify:tla`, `verify:smt`, `verify:kani`, `verify:spin`, `verify:csp`, `verify:lean`, `scripts/formal/verify-apalache.mjs`
- 統合実行: `pnpm run verify:formal`
- 集約: `pnpm run formal:summary`（`aggregate-formal.mjs` + `print-summary.mjs`）

**CSP(cspx) 拡張点**
- `verify:csp` は `CSP_RUN_CMD -> cspx -> refines -> cspmchecker` の順でバックエンド選択
- `cspx` 利用時は `csp-summary.json` と `cspx-result.json` を固定パス出力
- `schema_version=0.1` を互換基準とし、非互換は `status=unsupported` として要約
- `formal-aggregate.yml` の PR 集約は `backend/status/resultStatus/exitCode` を表示

## 3. リポジトリ構成（主要ディレクトリ）

| ディレクトリ | 役割 |
| --- | --- |
| `src/` | コア実装、CLI、MCPサーバー |
| `scripts/` | CI/品質/検証の自動化スクリプト |
| `docs/` | ドキュメント群 |
| `spec/` | 仕様レジストリと仕様定義 |
| `tests/` | テスト（ユニット、統合、プロパティ、レジリエンスなど） |
| `packages/` | サブパッケージ（spec-compiler 等） |
| `templates/` | 仕様・品質・CIのテンプレート |
| `artifacts/`, `reports/` | 実行結果・集約レポートの出力先 |
| `configs/` | TypeScript/テスト/CI設定類 |

## 4. 主要フロー

### 4.1 ローカル検証フロー（例）
1. 依存導入: `pnpm install`
2. 最小検証: `pnpm run lint`, `pnpm run test:fast`
3. 形式検証（任意）: `pnpm run verify:formal`

### 4.2 CIフロー（例）
1. PR作成
2. `verify-lite` / `policy-gate` / `gate`（Copilot Review Gate; `.github/workflows/copilot-review-gate.yml`）を中心に軽量ゲートを通過
3. 必要に応じて `run-formal` ラベルまたは `workflow_dispatch` で `formal-verify` を実行
4. 必要なら `enforce-formal` ラベルで Apalache `ran/ok` をゲート化

### 4.3 仕様検証フロー
1. 仕様の登録と更新（`spec/`）
2. `spec:validate` で構文検証
3. 形式検証で反例や不整合を検出

## 5. 成果物とトレーサビリティ

- `artifacts/` と `reports/` にCI成果物を集約
- 形式検証やテスト結果の要約は CI コメントと連動
- 形式検証の主成果物: `artifacts/hermetic-reports/formal/summary.json`
- CSP 詳細成果物: `artifacts/hermetic-reports/formal/csp-summary.json`, `artifacts/hermetic-reports/formal/cspx-result.json`
- トレーサビリティ設計は `docs/verify/TRACEABILITY-GUIDE.md` を参照

## 6. セキュリティとコンプライアンス

- セキュリティ検証ワークフロー: `security.yml`, `sbom-generation.yml`
- SBOM生成や依存監査を含む運用を想定

## 7. 制約と注意点
- 本プロダクトはCI/CDの定義と運用基盤を提供するが、運用代行は行いません
- エージェントの実行環境は外部に依存します
- `verify:lite` は `scripts/ci/run-verify-lite-local.sh` を通じて `pnpm types:check` / `pnpm lint` / `pnpm run build` を実行するため、JS/TS ツールチェーン前提です
- 他言語プロダクトは `verify:formal` / `verify:conformance` など仕様入力中心の機能を先行導入し、言語依存ゲートは別実装で接続する前提です

## 8. 関連資料
- 概要説明資料: `docs/product/OVERVIEW.md`
- 利用マニュアル: `docs/product/USER-MANUAL.md`
- 適用対象・入力/出力・ツール適性: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- 実装準拠の全体構成: `docs/architecture/CURRENT-SYSTEM-OVERVIEW.md`
- 全体ナビゲーション: `docs/README.md`
