---
docRole: derived
canonicalSource:
- docs/getting-started/QUICK-START-GUIDE.md
- .github/workflows/verify-lite.yml
- package.json
lastVerified: '2026-03-22'
---
# ae-framework Minimal Adoption（最小導入パッケージ）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
Establish the minimum PR-quality gate package at the lowest possible cost, while keeping heavier verification optional and opt-in.

### 2. Prerequisites
- Node.js `>=20.11 <23` (`package.json` `engines.node`)
- pnpm `10.0.0` (`package.json` `packageManager`)
- GitHub Actions as the CI execution surface

### 3. Minimum Adoption Set
#### 3.1 Local and CI commands
```bash
pnpm install
pnpm run lint
pnpm run test:fast
pnpm run verify:lite
```

#### 3.2 Minimum PR gate
Required checks on `main` should use:
- `verify-lite`
- `policy-gate`
- `gate`

References:
- `docs/ci/branch-protection-operations.md`
- `docs/ci/copilot-review-gate.md`

#### 3.3 Minimum artifacts
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/ci/policy-gate-summary.json`
- `artifacts/report-envelope.json`

`verify-lite` already validates summary and envelope schemas as part of the baseline workflow.

### 4. Minimum Responsibilities by Role
#### 4.1 PM / team lead
- Choose and apply the branch-protection preset
- Define the opt-in policy for heavy checks

#### 4.2 Developers
- Keep `lint`, `test:fast`, and `verify:lite` green
- Resolve Copilot review threads before merge

#### 4.3 QA / test operators
- Review the `verify-lite` summary first
- Request additional gates only when the summary or risk profile justifies it

#### 4.4 Operations / infrastructure
- Ensure CI permissions and required secrets exist
- Understand fork-PR limitations for security and SBOM workflows

### 5. Adoption Paths
#### 5.1 Standardize PR operation first
Start by making `verify-lite`, `policy-gate`, and `gate` the only required checks.

#### 5.2 Start specification operations
```bash
pnpm run spec:validate -i spec/example-spec.md --output .ae/ae-ir.json
pnpm run spec:lint -i .ae/ae-ir.json
```

#### 5.3 Add formal verification later
```bash
pnpm run tools:formal:check
pnpm run verify:formal
```

#### 5.4 Add heavy regression monitoring later
```bash
node scripts/pipelines/sync-test-results.mjs --store
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

#### 5.5 Add agent integration only when needed
```bash
pnpm run codex:run
```

### 6. Definition of Done
- `verify-lite` is green
- `policy-gate` is green
- `gate` is green
- Minimum artifacts are generated
- The team agrees on the opt-in rule for heavy checks

### 7. References
- `docs/product/USER-MANUAL.md`
- `docs/ci/label-gating.md`
- `docs/ci/branch-protection-operations.md`

---

## 日本語

## 1. 目的
最小コストで「**PR運用の品質ゲート**」を確立し、必要時にだけ重い検証を追加できる状態を作る。

## 2. 前提（根拠）
- Node.js `>=20.11 <23`（`package.json` の `engines.node`）
- pnpm `10.0.0`（`package.json` の `packageManager`）
- CI基盤: GitHub Actions（`.github/workflows/*`）

## 3. 最小導入セット（必須）

### 3.1 コマンド（ローカル/CI）
```bash
pnpm install
pnpm run lint
pnpm run test:fast
pnpm run verify:lite
```

### 3.2 PR運用（最小ゲート）
- Required checks:
  - `Verify Lite / verify-lite`
  - `Policy Gate / policy-gate`
  - `Copilot Review Gate / gate`
- 根拠: `docs/ci/branch-protection-operations.md`, `docs/ci/copilot-review-gate.md`

### 3.3 成果物（最小）
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/ci/policy-gate-summary.json`
- `artifacts/report-envelope.json`

> 補足: verify-lite ではサマリ/エンベロープのスキーマ検証が既に組み込まれています（`.github/workflows/verify-lite.yml`）。

## 4. 役割別の最小タスク

### 4.1 PM/リード
- Branch protection の preset を決定・適用  
  例: `.github/branch-protection.main.verify-lite-noreview.json`
- opt-in 運用ルールを定義（重い検証をいつ/誰が起動するか）

### 4.2 開発者
- `pnpm run lint` / `pnpm run test:fast` / `pnpm run verify:lite` を通す
- PRレビューでは **Copilot指摘の解決** を徹底する

### 4.3 QA/テスト担当
- verify-lite のサマリを確認し、必要時のみ追加ゲートを要求
- opt-in ラベル/Slash の選定（`docs/ci/label-gating.md`）

### 4.4 運用/インフラ
- CI実行権限と必要なSecretの有無を確認
- Fork PR の制限（security/SBOM）があることを把握

## 5. 目的別の導入パス（最小→拡張）

### 5.1 PR運用の標準化（最小）
- Required checks を `verify-lite` + `policy-gate` + `gate` に統一
- 追加検証は opt-in（`run-security`, `run-formal`, `run-resilience` など）
- （任意）Copilot→auto-fix→auto-merge により、レビュー対応とマージ操作を段階的に自動化できます（Repository Variables）。詳細: `docs/ci/pr-automation.md`

### 5.2 仕様運用を開始したい（最小）
```bash
pnpm run spec:validate -i spec/example-spec.md --output .ae/ae-ir.json
pnpm run spec:lint -i .ae/ae-ir.json
```

### 5.3 形式検証を追加したい（opt-in）
```bash
pnpm run tools:formal:check
pnpm run verify:formal
```
※ ローカルでの実行可否はツール導入状況に依存

### 5.4 重い検証の退行監視（opt-in）
```bash
node scripts/pipelines/sync-test-results.mjs --store
node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json
```

### 5.5 エージェント統合（必要時）
```bash
pnpm run codex:run
```
詳細: `docs/codex/ae-playbook.md`

## 6. DoD（受け入れ基準）
- [ ] verify-lite がグリーンである
- [ ] Copilot Review Gate がグリーンである
- [ ] 最小成果物（verify-lite summary / report envelope）が生成される
- [ ] opt-in 運用ルールがチーム内で合意されている

## 7. 参照
- `docs/product/USER-MANUAL.md`
- `docs/ci/label-gating.md`
- `docs/ci/branch-protection-operations.md`
