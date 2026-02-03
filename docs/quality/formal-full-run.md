# Formal Full Run (All Tools Smoke Test)

> 🌍 Language / 言語: English | 日本語

---

## English

This guide shows how to run **all formal verification tools** end-to-end for a smoke test.

### Recommended: CI (covers Apalache / SMT / Alloy / TLA / Kani)

1) **Label-gated (PR)**
- Add label `run-formal` to the PR.
- Optional: add `enforce-formal` to gate Apalache `ran/ok`.

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
- `formal-reports-smt`: `smt-summary.json`
- `formal-reports-alloy`: `alloy-summary.json`
- `formal-reports-tla`: `tla-summary.json`
- `formal-reports-kani`: `kani-summary.json`

### Local (when you want a quick smoke test)

Pre-reqs:
- Node.js + pnpm
- Java 17
- `TLA_TOOLS_JAR` for TLC (see `docs/quality/formal-tools-setup.md`)
- z3/cvc5 for SMT
- Optional: Alloy jar, Apalache, Kani

#### 1) Base run (conformance + alloy + TLA + SMT + aggregate)
```bash
pnpm install
pnpm run verify:formal
```

Notes:
- Alloy needs `ALLOY_JAR` or `ALLOY_RUN_CMD` to run (otherwise `tool_not_available`).
- SMT needs an input file to run. Use the sample below.

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

#### 6) Model check (TLC/Alloy scan)
```bash
npm run verify:model
```

Outputs:
- `artifacts/hermetic-reports/formal/*.json`
- `artifacts/hermetic-reports/conformance/summary.json`
- `artifacts/codex/model-check.json`

---

## 日本語

この手順は、**すべての形式検査ツールをまとめて動作確認**するためのスモークテストです。

### 推奨: CI（Apalache / SMT / Alloy / TLA / Kani をまとめて実行）

1) **PRラベル実行**
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

### ローカル（簡易スモークテスト）

前提:
- Node.js + pnpm
- Java 17
- TLC 用の `TLA_TOOLS_JAR`（`docs/quality/formal-tools-setup.md` 参照）
- SMT ソルバ（z3/cvc5）
- 任意: Alloy jar / Apalache / Kani

#### 1) ベース実行（conformance + alloy + TLA + SMT + 集約）
```bash
pnpm install
pnpm run verify:formal
```

補足:
- Alloy は `ALLOY_JAR` / `ALLOY_RUN_CMD` 未設定だと `tool_not_available` になります。
- SMT は入力ファイル指定が必要です（次の手順）。

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

#### 6) モデル検査（TLC/Alloy スキャン）
```bash
npm run verify:model
```

成果物:
- `artifacts/hermetic-reports/formal/*.json`
- `artifacts/hermetic-reports/conformance/summary.json`
- `artifacts/codex/model-check.json`
