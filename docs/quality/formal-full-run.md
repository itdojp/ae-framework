---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- docs/quality/formal-tools-setup.md
lastVerified: '2026-04-11'
---
# Formal Full Run (All Tools Smoke Test)

> 🌍 Language / 言語: English | 日本語

---

## English

This guide shows how to run **all formal verification tools** end-to-end for a smoke test.

### Recommended: CI (covers Apalache / SMT / Alloy / TLA / Kani / SPIN / Lean; CSP runs via cspx as non-blocking)

1) **Label-gated (PR)**
- Add label `run-formal` to the PR.
- Optional: add `enforce-formal` to gate Apalache `ran/ok` and enforce Formal Summary v1 schema.

2) **Manual (workflow_dispatch)**
- Actions → **Formal Verify** → Run workflow
  - `target`: `all`
  - `engine`: `tlc` or `apalache` (for TLA)
  - `solver`: `z3` or `cvc5` (for SMT)
  - `alloyJar` / `tlaToolsJar`: optional jar path overrides

3) **Artifacts to confirm**
- `formal-reports` artifact (folder): `artifacts/hermetic-reports/formal/*`
- `formal-reports-conformance`: `conformance-summary.json`
- `formal-reports-apalache`: `apalache-summary.json`, `apalache-output.txt`
- `formal-reports-smt`: `smt-summary.json`, `smt-output.txt`
- `formal-reports-alloy`: `alloy-summary.json`, `alloy-output.txt`
- `formal-reports-tla`: `tla-summary.json`, `tla-output.txt`
- `formal-reports-kani`: `kani-summary.json`
- `formal-reports-spin`: `spin-summary.json`, `spin-output.txt`
- `formal-reports-csp`: `csp-summary.json`, `csp-output.txt`, `cspx-result.json`
- `formal-reports-lean`: `lean-summary.json`, `lean-output.txt`
- `formal-summary-v1`: `artifacts/formal/formal-summary-v1.json` (normalized)

### Local (when you want a quick smoke test)

Pre-reqs:
- Node.js + pnpm
- Java 17
- `TLA_TOOLS_JAR` for TLC (see `docs/quality/formal-tools-setup.md`)
- z3/cvc5 for SMT
- Optional: Alloy jar, Apalache, Kani
- Optional: SPIN (`spin` + `gcc`)
- Optional: Lean4 (`elan` + `lake`)
- Optional: CSP tool (`cspx` recommended; or `refines`/`cspmchecker`, or configure via `CSP_RUN_CMD`)

#### 1) Base run (conformance + alloy + TLA + SMT + Apalache + Kani + SPIN + CSP + Lean + aggregate)
```bash
pnpm install
pnpm run verify:formal
```

Notes:
- Alloy needs `ALLOY_JAR` or `ALLOY_RUN_CMD` to run (otherwise `tool_not_available`).
- SMT needs an input file to run. Use the sample below.
- SPIN/Lean/CSP are non-blocking; if tools are not installed, they will report `tool_not_available`.

#### 2) Ensure SMT actually runs
```bash
pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2
```

#### 3) Run Alloy with jar (headless)
```bash
mkdir -p .cache/tools
curl -L -sS -o .cache/tools/alloy.jar \
  "https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar"

ALLOY_JAR=$PWD/.cache/tools/alloy.jar \
ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' \
  pnpm run verify:alloy -- --file spec/alloy/Domain.als
```

#### 4) Run Apalache (if installed)
```bash
node scripts/formal/verify-apalache.mjs --file spec/tla/DomainSpec.tla
```

#### 5) Run Kani (if installed)
```bash
node scripts/formal/verify-kani.mjs
```

#### 6) Run SPIN (if installed)
```bash
pnpm run verify:spin -- --file spec/spin/sample.pml --ltl p_done
```

#### 7) Run Lean4 (if installed)
```bash
pnpm run verify:lean
```

#### 8) Run CSP (when configured)
```bash
# Typecheck (safe default):
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck

# If you want to run the richer CSPM sample (may require a different backend/tool support):
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode typecheck

# Assertions (backend-dependent):
# - cspx: runs a basic deadlock freedom check (v0.1: may fail for STOP-only samples)
# - refines (FDR): runs assertions embedded in the file
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode assertions

# Or, run via custom backend command (shell). {file} is replaced with the absolute file path:
CSP_RUN_CMD='echo Running CSP tool on {file}' pnpm run verify:csp -- --file spec/csp/sample.cspm --mode typecheck
```

For details (artifacts / example outputs), see: [formal-csp.md](./formal-csp.md).
For implementation-aligned architecture context, see: [CURRENT-SYSTEM-OVERVIEW.md](../architecture/CURRENT-SYSTEM-OVERVIEW.md).
Upstream cspx references:
- https://github.com/itdojp/cspx/blob/main/docs/integrations/ae-framework.md
- https://github.com/itdojp/cspx/blob/main/docs/validation-report.md

#### 9) Model check (TLC/Alloy scan)
```bash
pnpm run verify:model
```

Outputs:
- `artifacts/hermetic-reports/formal/*.json`
- `artifacts/hermetic-reports/conformance/summary.json`
- `artifacts/codex/model-check.json`

---

## 日本語

この手順は、**すべての形式検査ツールをまとめて動作確認**するためのスモークテストです。

### 推奨: CI（Apalache / SMT / Alloy / TLA / Kani / SPIN / Lean をまとめて実行。CSP は cspx 経由で非ブロッキング）

1) **PR ラベルで実行**
- PR に `run-formal` ラベルを付与
- 必要に応じて `enforce-formal` で Apalache の ran/ok をゲート

2) **手動実行（workflow_dispatch）**
- Actions → **Formal Verify** → Run workflow
  - `target`: `all`
  - `engine`: `tlc` or `apalache`
  - `solver`: `z3` or `cvc5`
  - `alloyJar` / `tlaToolsJar`: 任意（jar パス上書き）

3) **成果物の確認**
- `formal-reports`（`artifacts/hermetic-reports/formal/*`）
- `formal-reports-conformance`（`conformance-summary.json`）
- `formal-reports-apalache`（`apalache-summary.json`, `apalache-output.txt`）
- `formal-reports-smt`（`smt-summary.json`）
- `formal-reports-alloy`（`alloy-summary.json`）
- `formal-reports-tla`（`tla-summary.json`）
- `formal-reports-kani`（`kani-summary.json`）
- `formal-reports-spin`（`spin-summary.json`）
- `formal-reports-csp`（`csp-summary.json`, `cspx-result.json`）
- `formal-reports-lean`（`lean-summary.json`）

### ローカル（簡易スモークテスト）

前提:
- Node.js + pnpm
- Java 17
- TLC 用の `TLA_TOOLS_JAR`（`docs/quality/formal-tools-setup.md` 参照）
- SMT ソルバ（z3/cvc5）
- 任意: Alloy jar / Apalache / Kani
- 任意: SPIN（`spin` + `gcc`）
- 任意: Lean4（`elan` + `lake`）
- 任意: CSP ツール（`cspx` 推奨、または `refines` / `cspmchecker` / `CSP_RUN_CMD`）

#### 1) ベース実行（conformance + alloy + TLA + SMT + Apalache + Kani + SPIN + CSP + Lean + 集約）
```bash
pnpm install
pnpm run verify:formal
```

補足:
- Alloy は `ALLOY_JAR` / `ALLOY_RUN_CMD` 未設定だと `tool_not_available` になります。
- SMT は入力ファイル指定が必要です（次の手順）。
- SPIN / Lean / CSP は非ブロッキングです。未導入の場合は `tool_not_available` として記録されます。

#### 2) SMT を実行
```bash
pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2
```

#### 3) Alloy を jar で実行（ヘッドレス）
```bash
mkdir -p .cache/tools
curl -L -sS -o .cache/tools/alloy.jar \
  "https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar"

ALLOY_JAR=$PWD/.cache/tools/alloy.jar \
ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' \
  pnpm run verify:alloy -- --file spec/alloy/Domain.als
```

#### 4) Apalache を実行（インストール済みの場合）
```bash
node scripts/formal/verify-apalache.mjs --file spec/tla/DomainSpec.tla
```

#### 5) Kani を実行（インストール済みの場合）
```bash
node scripts/formal/verify-kani.mjs
```

#### 6) SPIN を実行（インストール済みの場合）
```bash
pnpm run verify:spin -- --file spec/spin/sample.pml --ltl p_done
```

#### 7) Lean4 を実行（インストール済みの場合）
```bash
pnpm run verify:lean
```

#### 8) CSP を実行（設定済みの場合）
```bash
# Typecheck（安全な既定）:
pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck

# より豊富な CSPM サンプルを実行したい場合（バックエンド/ツール側の対応が必要な場合があります）:
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode typecheck

# Assertions（バックエンド依存）:
# - cspx: 基本のデッドロック検査（v0.1: STOPのみのサンプルでは失敗します）
# - refines（FDR）: ファイル内の assertion を実行
pnpm run verify:csp -- --file spec/csp/sample.cspm --mode assertions

# 任意のバックエンドをコマンドで実行（シェル経由）。{file} は絶対パスへ置換されます:
CSP_RUN_CMD='echo Running CSP tool on {file}' pnpm run verify:csp -- --file spec/csp/sample.cspm --mode typecheck
```

詳細（成果物/実行結果例）は [formal-csp.md](./formal-csp.md) を参照してください。
現行実装準拠の全体構成は [CURRENT-SYSTEM-OVERVIEW.md](../architecture/CURRENT-SYSTEM-OVERVIEW.md) を参照してください。
上流 cspx の参照先:
- https://github.com/itdojp/cspx/blob/main/docs/integrations/ae-framework.md
- https://github.com/itdojp/cspx/blob/main/docs/validation-report.md

#### 9) モデル検査（TLC/Alloy スキャン）
```bash
pnpm run verify:model
```

成果物:
- `artifacts/hermetic-reports/formal/*.json`
- `artifacts/hermetic-reports/conformance/summary.json`
- `artifacts/codex/model-check.json`
