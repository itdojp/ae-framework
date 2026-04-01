---
docRole: ssot
lastVerified: '2026-04-02'
owner: formal-methods
verificationCommand: pnpm -s run check:doc-consistency
---
# Formal Runbook (low-impact start)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

負担の小さい形式検査の運用手順です。PR ラベルでの起動（`run-formal`）、手動トリガー、CLI スタブ、仕様/アーティファクトの配置、ロードマップ適合を簡潔にまとめています。
全ツールのスモークテスト手順は `docs/quality/formal-full-run.md` を参照してください。

## English

### Purpose
This runbook describes the lowest-friction way to operate formal verification in this repository. It focuses on label-gated CI (`run-formal`), manual `workflow_dispatch`, local non-blocking runners, artifact locations, and the current roadmap fit. For full smoke-test coverage across all supported tools, see `docs/quality/formal-full-run.md`.

### Usage (CI / Labels)
- Label-gated CI: add PR label `run-formal` to trigger the formal lane. The lane starts as report-only.
- Enforcement: add PR label `enforce-formal` to make the Apalache result (`ok == true`) blocking in the strict path.
- Manual run: trigger `Formal Verify` via `workflow_dispatch`.
  - `target`: `all|conformance|alloy|tla|smt|apalache|kani|spin|csp|lean`
  - `engine`: `tlc|apalache` (for TLA)
  - `solver`: `z3|cvc5` (for SMT)
  - `alloyJar`: optional path to the Alloy jar
  - `tlaToolsJar`: optional path to `tla2tools.jar`

### CLI Runners (non-blocking)
- `pnpm run verify:conformance` - conformance summary runner. Use together with `ae conformance verify` when you need a narrower replay/conformance check.
- `pnpm run verify:alloy` - Alloy runner. Resolves `ALLOY_RUN_CMD`, `ALLOY_JAR`, or the `alloy` CLI.
- `pnpm run verify:tla -- --engine=apalache|tlc` - TLA runner. Resolves `TLA_TOOLS_JAR` or `apalache`.
- `pnpm run verify:smt -- --solver=z3|cvc5` - SMT runner.
- `pnpm run verify:kani` - Kani presence summary runner.
- `pnpm run verify:spin` - Promela/SPIN runner.
- `pnpm run verify:csp` - CSP runner using `CSP_RUN_CMD`, `cspx`, `refines`, or `cspmchecker`.
  - When `cspx` is used, the runner emits `csp-summary.json` and `cspx-result.json`.
  - A `schema_version` mismatch (expected `0.1`) is recorded as `status: "unsupported"`.
  - Detailed examples: `docs/quality/formal-csp.md`.
- `pnpm run verify:lean` - Lean4 `lake build` runner.
- `pnpm run verify:formal` - chained local runner for the commands above.
  - Writes the aggregate summary to `artifacts/hermetic-reports/formal/summary.json`.
  - Prints a compact post-run summary to the console.

### Runtime Hooks (Phase 2.2)
- Optional runtime hook JSON can be stored at `artifacts/hermetic-reports/runtime/hooks.json` and correlated with replay summaries by the conformance driver.
- Environment variables:
  - `RUNTIME_HOOKS` or `CONFORMANCE_RUNTIME_HOOKS` - path to the hook JSON.
  - `CONFORMANCE_TRACE` - replay summary path. Default: `artifacts/domain/replay.summary.json`.
- `conformance-summary` adds `runtimeHooks: {present, path, count, uniqueEvents[], traceId, matchesReplayTraceId}`.

### BDD to LTL suggestions (report-only)
- `pnpm run bdd:suggest` extracts GWT scenarios from `spec/bdd/**/*.feature` (fallback: `features/`) and generates candidate LTL properties.
- Outputs:
  - `artifacts/bdd/scenarios.json` - PR-summary input containing `{title, criteriaCount}`.
  - `artifacts/properties/ltl-suggestions.json` - aggregate/reference output containing `{count, items[]}`.

### Reproduce locally
- Tool availability: `pnpm run tools:formal:check`.
- Apalache (when installed): `pnpm run verify:tla -- --engine=apalache`.
- TLC (when `TLA_TOOLS_JAR` is set): `TLA_TOOLS_JAR=/path/to/tla2tools.jar pnpm run verify:tla -- --engine=tlc`.
- SMT (when `z3` or `cvc5` is available): `pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2`.

### Apalache quickstart
- Presence/version check: `node scripts/formal/check-apalache.mjs`.
- Verify (non-blocking summary): `node scripts/formal/verify-apalache.mjs --file spec/tla/DomainSpec.tla`.
- If a sibling `*.cfg` exists (for example `spec/tla/DomainSpec.cfg`), the runner automatically appends `--config`.
- Notes:
  - `verify:apalache` is already wired as a non-blocking presence/version guard in `formal-verify`.
  - The aggregate comment emits one-line Apalache `ran/ok` status plus a trimmed error fragment when present.

### Timeouts
- TLA and SMT runners support `--timeout <ms>` to avoid long-running local jobs when GNU `timeout` is available.
- Example: `pnpm run verify:tla -- --engine=apalache --timeout 60000`.
- On timeout, the summary is written with `status: "timeout"` and the lane remains non-blocking unless a stricter consumer decides otherwise.

### Troubleshooting
- PATH: if `apalache` or `apalache-mc` is missing, run `node scripts/formal/check-apalache.mjs` to verify presence and version.
- Timeout: when logs continue indefinitely, set `--timeout` and use the aggregate comment's `status: "timeout"` as the cutoff signal.
- CSP unsupported:
  - If `artifacts/hermetic-reports/formal/csp-summary.json` has `status: "unsupported"` and `output` or `outputFile` (for example `artifacts/hermetic-reports/formal/csp-output.txt`) contains `--summary-json` CLI errors such as `unexpected argument`, `unknown argument`, or `wasn't expected`, the installed `cspx` is too old.
  - Confirm support with `cspx typecheck --help | grep -- --summary-json`, then update via the pinned setup in `docs/quality/formal-tools-setup.md`. `CSP_RUN_CMD` remains the fallback escape hatch.
  - If the failure is `schema_version mismatch`, inspect `cspx-result.json` and update `cspx` until it matches the current contract (`schema_version=0.1`).
  - Detailed CSP notes: `docs/quality/formal-csp.md`.
- Logs:
  - Raw logs are written to `artifacts/hermetic-reports/formal/<tool>-output.txt`.
  - Examples: `apalache-output.txt`, `tla-output.txt`, `smt-output.txt`, `alloy-output.txt`, `spin-output.txt`, `csp-output.txt`, `lean-output.txt`.
  - In Formal Summary v1/v2, `results[].logPath` stores the repo-relative log path when a log file exists.

### Advanced toggles
- Aggregate wrap width: `FORMAL_AGG_WRAP_WIDTH` (`0` disables wrapping; `80-100` is the practical range).
- Apalache error extraction limit / line clamp: `APALACHE_ERRORS_LIMIT` / `APALACHE_ERROR_LINE_CLAMP` (defaults: `5` / `200`).
- Apalache output preview clamp: `APALACHE_OUTPUT_CLAMP` (default: `4000`).
  - Applies to `artifacts/hermetic-reports/formal/apalache-summary.json` -> `output`.

### Aggregate JSON validation (non-blocking)
- The aggregate workflow emits `artifacts/formal/formal-aggregate.json` and validates it against a lightweight schema at warning level.
- Local check: `node scripts/formal/validate-aggregate-json.mjs`.
  - When the file is missing or malformed, the helper emits `::warning::` rather than failing the local flow.

### Formal Summary v1/v2 (dual-write + dual-validate)
- Producer: `scripts/formal/generate-formal-summary-v1.mjs` writes v1 with `--out` and v2 with `--out-v2`.
- Current outputs:
  - `artifacts/formal/formal-summary-v1.json` (schema: `schema/formal-summary-v1.schema.json`)
  - `artifacts/formal/formal-summary-v2.json` (schema: `schema/formal-summary-v2.schema.json`, `schemaVersion=formal-summary/v2`, `contractId=formal-summary.v2`)
- Local dual-validate:
  - `node scripts/ci/validate-formal-summary-v1.mjs artifacts/formal/formal-summary-v1.json schema/formal-summary-v1.schema.json`
  - `node scripts/ci/validate-formal-summary-v2.mjs artifacts/formal/formal-summary-v2.json schema/formal-summary-v2.schema.json`
- CI dual-validate:
  - `scripts/ci/validate-artifacts-ajv.mjs` validates both versions.
  - `.github/workflows/formal-aggregate.yml` requires both files under strict mode (`enforce-formal`) via `--require`.
- Consumer:
  - `scripts/ci/generate-run-manifest.mjs` reads them as `formalSummaryV1` / `formalSummaryV2`.
- One-line local inspection:
  - `node -e "const p='artifacts/formal/formal-aggregate.json';const j=require('fs').existsSync(p)?require('./'+p):null;if(!j){console.log('no aggregate');process.exit(0)}const pr=j.info?.present||{};const keys=Object.entries(pr).filter(([,v])=>v).map(([k])=>k);const total=(typeof j.info?.presentTotal==='number')?j.info.presentTotal:Object.keys(pr).length;console.log('Present:', keys.length+'/'+total, keys.length?('('+keys.join(', ')+')'):'');"`
  - jq examples:
    - `jq '.info.presentCount' artifacts/formal/formal-aggregate.json`
    - `jq '.info.presentTotal' artifacts/formal/formal-aggregate.json`
    - `jq -r '.info.present | to_entries | map("\(.key)=\(.value|tostring)") | join(", ")' artifacts/formal/formal-aggregate.json`
    - `jq -r '.info.ranOk.apalache' artifacts/formal/formal-aggregate.json`

### Aggregate JSON conventions
- Single source of truth:
  - `artifacts/formal/formal-aggregate.json` is the canonical source for `present`, `ran`, and `ok` signals.
  - PR comments should be generated from that aggregate.
- Comment wrapping:
  - Enable with `FORMAL_AGG_WRAP_WIDTH`.
  - Recommended value: `80-100` if you need wrapping.
  - Keep it disabled when the comment contains many long URLs or tables.
- Quick trade-off:
  - Pros: easier reading for long lines and less horizontal scrolling.
  - Cons: tables and long URLs can become visually noisy.
- Key fields:
  - `info.present` - presence flags for `tla`, `alloy`, `smt`, `apalache`, `conformance`, `kani`, `spin`, `csp`, `lean`.
  - `info.presentCount` - number of summaries currently present.
  - `info.presentTotal` - denominator for the tracked summaries.
  - `info.ranOk.apalache` - `{ ran: boolean, ok: boolean|null }`, where `null` means indeterminate.

### Console summary reference
- Example log when `run-formal` is present:
```text
--- Formal Summary ---
Conformance: schemaErrors=0, invariantViolations=1, rate=0.333, first=allocated_le_onhand@2
SMT: ran
Alloy: tool_not_available
TLA: tool_not_available (tlc)
----------------------
```
- Console color meaning:
  - Green: successful run with no violation.
  - Yellow: warning, violation, or skip.
  - Gray: informational state such as tool missing.
- Normalized status rules:
  - Conformance: `[OK]` when `schemaErrors=0` and `invariantViolations=0`, otherwise `[WARN]`.
  - SMT: `[OK]` when it ran (`status=ran`), `[INFO]` when the solver is unavailable, otherwise `[WARN]`.
  - Alloy: `[OK]` when it ran (`status=ran`), `[INFO]` when the tool is unavailable, otherwise `[WARN]`.
  - TLA: `[OK]` when it ran (`status=ran`), `[INFO]` when the tool is unavailable, otherwise `[WARN]`.

### Conformance sample (quick demo)
- `pnpm run conformance:sample` - generate sample rules, settings, data, and context.
- `pnpm run conformance:verify:sample` - run verification against the generated sample and emit JSON reports.
- `pnpm run conformance:report` - aggregate `artifacts/conformance/conformance-results.json` and `artifacts/hermetic-reports/conformance/*.json` into `reports/conformance/conformance-summary.(json|md)` (use `--output` / `--markdown-output` to customize filenames if needed).
- `pnpm bdd` - run encrypted-chat BDD scenarios and save snapshots to `artifacts/bdd/encrypted-chat/*.json`.
- `pnpm pipelines:pact` - run Pact contract tests for the encrypted-chat API in `tests/contracts/encrypted-chat-contracts.test.ts`.

### Minimal YAML (example)
```yaml
name: Formal Verify
on:
  pull_request:
    types: [labeled, synchronize]
jobs:
  verify:
    if: contains(github.event.pull_request.labels.*.name, 'run-formal')
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - run: pnpm run verify:formal
```

### Specs / Artifacts
- TLA+: `spec/tla/` (README plus skeleton)
- Alloy 6: `spec/alloy/` (README plus skeleton)
- Trace schema: `observability/trace-schema.yaml`
- Reports: `artifacts/hermetic-reports/`
  - Apalache: `artifacts/hermetic-reports/formal/apalache-summary.json`, `artifacts/hermetic-reports/formal/apalache-output.txt`
  - Formal summary: `artifacts/hermetic-reports/formal/summary.json` (includes `present`, `conformance`, `smt`, `alloy`, `tla`, `apalache`)
  - Metadata: `generatedAtUtc`, `generatedAtLocal`, `timezoneOffset`, `gitCommit`, `branch`, `runner`, `toolVersions`
  - Conformance report outputs: `reports/conformance/conformance-summary.json` / `reports/conformance/conformance-summary.md` (use explicit `--output` / `--markdown-output` flags when a workflow needs different filenames such as `verify-lite-summary.*`)

### Samples
- TLA+: `spec/tla/DomainSpec.tla` - minimal safety invariant and transition example.
- Alloy: `spec/alloy/Domain.als` - minimal safety assertion example.

### Tools
- Local availability check: `pnpm run tools:formal:check`
- Setup instructions: `docs/quality/formal-tools-setup.md`
- CI split / operating patterns: `docs/quality/formal-ops-guidelines.md`
- Lightweight trace validation: `pnpm run trace:validate`
- SMT sample: `spec/smt/sample.smt2`
- Example SMT run: `pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2`
- Alloy / TLA jar configuration:
  - set `alloyJar` / `tlaToolsJar` in `workflow_dispatch`
  - or set `ALLOY_JAR` / `TLA_TOOLS_JAR` locally

### `verify:conformance` options
- `-i, --in <file>` - input event JSON. Default: `samples/conformance/sample-traces.json`.
- `--schema <file>` - trace schema YAML. Default: `observability/trace-schema.yaml`.
- `--out <file>` - output path. Default: `artifacts/hermetic-reports/conformance/summary.json`.
- `--disable-invariants <list>` - comma-separated invariants to disable, for example `allocated_le_onhand,onhand_min`.
- `--onhand-min <number>` - minimum `onHand` value. Default: `0`.

### Notes and roadmap fit
- `samples/conformance/sample-traces.json` ships with the repository and is the default input for both `verify:conformance` and `trace:validate`.
- Roadmap Fit (Issue #493):
  - start with non-blocking, label-gated CI
  - wire real engines behind the stubs incrementally

### Reading the conformance summary
- `events` - input event count.
- `schemaErrors` - schema violation count.
- `invariantViolations` - invariant violation count. `violationRate` is normalized by `events`.
- `firstInvariantViolation` - first violation with `type` and `index`.
- `byType(...)` - per-invariant counts such as `onhand_min` and `allocated_le_onhand`.

### Local command examples
- TLA+ (TLC)
  - `java -cp $TLA_TOOLS_JAR tlc2.TLC spec/tla/DomainSpec.tla`
  - On failure, inspect the log for `TLC FAILED` or `Invariant violated`.
- Apalache
  - `apalache-mc version`
  - `apalache-mc check --inv=Invariant spec/tla/DomainSpec.tla`
- SMT (standalone availability check)
  - `z3 --version` / `cvc5 --version`
  - In normal operation, prefer `pnpm run verify:smt -- --solver=z3|cvc5`.
- Alloy CLI (when available)
  - `pnpm run verify:alloy -- --file spec/alloy/Domain.als`

## 日本語（詳細）

### 運用の基本
1) PR でフォーマル検査を走らせたい場合は、ラベル `run-formal` を付与（初期はスタブ）。
2) 手動実行は GitHub Actions の `workflow_dispatch`（Formal Verify）から起動。

### CLI ランナー（非ブロッキング）
- `pnpm run verify:conformance` - conformance summary runner。必要に応じて `ae conformance verify` と併用する。
- `pnpm run verify:alloy` - Alloy runner。`ALLOY_RUN_CMD`、`ALLOY_JAR`、`alloy` CLI を順に解決する。
- `pnpm run verify:tla -- --engine=apalache|tlc` - TLA runner。`TLA_TOOLS_JAR` または `apalache` を解決する。
- `pnpm run verify:smt -- --solver=z3|cvc5` - SMT runner。
- `pnpm run verify:kani` - Kani presence summary runner。
- `pnpm run verify:spin` - Promela / SPIN runner。
- `pnpm run verify:csp` - `CSP_RUN_CMD`、`cspx`、`refines`、`cspmchecker` を順に使う CSP runner。
  - `cspx` を使う場合は `csp-summary.json` と `cspx-result.json` を出力する。
  - `schema_version` 不一致（期待値 `0.1`）は `status: "unsupported"` として記録する。
  - 詳細例は `docs/quality/formal-csp.md` を参照する。
- `pnpm run verify:lean` - Lean4 `lake build` runner。
- `pnpm run verify:formal` - 上記コマンドを連続実行する chained local runner。
  - 集約 summary は `artifacts/hermetic-reports/formal/summary.json` に出力される。
  - 実行後は compact な要約を console に表示する。

### Runtime Hooks（Phase 2.2）
- 任意の runtime hook JSON は `artifacts/hermetic-reports/runtime/hooks.json` に置き、conformance driver が replay summary と相関付ける。
- 環境変数:
  - `RUNTIME_HOOKS` または `CONFORMANCE_RUNTIME_HOOKS` - hook JSON path
  - `CONFORMANCE_TRACE` - replay summary path。既定: `artifacts/domain/replay.summary.json`
- `conformance-summary` は `runtimeHooks: {present, path, count, uniqueEvents[], traceId, matchesReplayTraceId}` を出力する。

### BDD -> LTL suggestions（report-only）
- `pnpm run bdd:suggest` は `spec/bdd/**/*.feature`（fallback: `features/`）から GWT scenario を抽出し、candidate LTL properties を生成する。
- 出力:
  - `artifacts/bdd/scenarios.json` - PR summary 入力（`{title, criteriaCount}`）
  - `artifacts/properties/ltl-suggestions.json` - 集約 / 参照出力（`{count, items[]}`）

### ローカル再現
- ツール有無の確認: `pnpm run tools:formal:check`
- Apalache（導入済みの場合）: `pnpm run verify:tla -- --engine=apalache`
- TLC（`TLA_TOOLS_JAR` 設定時）: `TLA_TOOLS_JAR=/path/to/tla2tools.jar pnpm run verify:tla -- --engine=tlc`
- SMT（`z3` または `cvc5` がある場合）: `pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2`

### Apalache quickstart
- Presence / version check: `node scripts/formal/check-apalache.mjs`
- Verify（non-blocking summary）: `node scripts/formal/verify-apalache.mjs --file spec/tla/DomainSpec.tla`
- sibling の `*.cfg`（例: `spec/tla/DomainSpec.cfg`）が存在する場合、runner は自動で `--config` を追加する。
- 補足:
  - `verify:apalache` は `formal-verify` 内で non-blocking presence/version guard として配線済み。
  - aggregate comment は Apalache の `ran/ok` と短い error fragment を 1 行で出力する。

### Timeouts
- TLA / SMT runner は GNU `timeout` が利用可能な環境で `--timeout <ms>` を受け付ける。
- 例: `pnpm run verify:tla -- --engine=apalache --timeout 60000`
- timeout 時は summary に `status: "timeout"` を書き込み、stricter consumer がない限り lane 自体は non-blocking のままにする。

### Troubleshooting
- PATH: `apalache` または `apalache-mc` が見つからない場合は `node scripts/formal/check-apalache.mjs` で presence/version を確認する。
- Timeout: log が止まらない場合は `--timeout` を付け、aggregate comment の `status: "timeout"` を cut-off signal として扱う。
- CSP unsupported:
  - `artifacts/hermetic-reports/formal/csp-summary.json` の `status: "unsupported"` と、`artifacts/hermetic-reports/formal/csp-output.txt` などに `--summary-json` の CLI error（`unexpected argument` / `unknown argument` / `wasn't expected`）が出ている場合、`cspx` が古い。
  - `cspx typecheck --help | grep -- --summary-json` で対応を確認し、`docs/quality/formal-tools-setup.md` の pinned setup に沿って更新する。`CSP_RUN_CMD` は fallback escape hatch として残る。
  - `schema_version mismatch` の場合は `cspx-result.json` を確認し、current contract（`schema_version=0.1`）に合うまで `cspx` を更新する。
- Raw logs:
  - `artifacts/hermetic-reports/formal/<tool>-output.txt` に保存される。
  - 例: `apalache-output.txt`, `tla-output.txt`, `smt-output.txt`, `alloy-output.txt`, `spin-output.txt`, `csp-output.txt`, `lean-output.txt`
  - Formal Summary v1/v2 では、log file が存在する場合 `results[].logPath` に repo-relative path が入る。

### Aggregate JSON validation（non-blocking）
- aggregate workflow は `artifacts/formal/formal-aggregate.json` を出力し、軽量 schema で warning-level validate を行う。
- ローカル check: `node scripts/formal/validate-aggregate-json.mjs`
- file が欠損または malformed でも、helper は local flow を fail させず `::warning::` を出す。

### Formal Summary v1/v2（dual-write + dual-validate）
- producer: `scripts/formal/generate-formal-summary-v1.mjs` が v1 を `--out`、v2 を `--out-v2` に出力する。
- current outputs:
  - `artifacts/formal/formal-summary-v1.json`（schema: `schema/formal-summary-v1.schema.json`）
  - `artifacts/formal/formal-summary-v2.json`（schema: `schema/formal-summary-v2.schema.json`、`schemaVersion=formal-summary/v2`、`contractId=formal-summary.v2`）
- local dual-validate:
  - `node scripts/ci/validate-formal-summary-v1.mjs artifacts/formal/formal-summary-v1.json schema/formal-summary-v1.schema.json`
  - `node scripts/ci/validate-formal-summary-v2.mjs artifacts/formal/formal-summary-v2.json schema/formal-summary-v2.schema.json`
- CI dual-validate:
  - `scripts/ci/validate-artifacts-ajv.mjs` が両 version を validate する。
  - `.github/workflows/formal-aggregate.yml` は strict mode（`enforce-formal`）で両 file を `--require` する。
- consumer:
  - `scripts/ci/generate-run-manifest.mjs` は `formalSummaryV1` / `formalSummaryV2` として読む。

### Aggregate JSON conventions
- single source of truth:
  - `artifacts/formal/formal-aggregate.json` が `present` / `ran` / `ok` signal の canonical source。
  - PR comment はこの aggregate から生成する。
- comment wrapping:
  - `FORMAL_AGG_WRAP_WIDTH` で有効化する。
  - 実用値は `80-100`、`0` は wrapping 無効。
  - 長い URL や table が多い場合は無効のままにする。
- key fields:
  - `info.present` - `tla`, `alloy`, `smt`, `apalache`, `conformance`, `kani`, `spin`, `csp`, `lean` の presence flag
  - `info.presentCount` - present な summary 数
  - `info.presentTotal` - 追跡対象 summary の分母
  - `info.ranOk.apalache` - `{ ran: boolean, ok: boolean|null }`。`null` は indeterminate

### 仕様/成果物配置
- TLA+: `spec/tla/`（最小スケルトンあり）
- Alloy 6: `spec/alloy/`（最小スケルトンあり）
- トレーススキーマ: `observability/trace-schema.yaml`
- レポート（計画）: `artifacts/hermetic-reports/`

### 環境変数（出力の調整）
- verify-apalache.mjs（要約の整形）
  - `APALACHE_ERRORS_LIMIT`（既定 5）: errors[] に採用する最大行数
  - `APALACHE_ERROR_LINE_CLAMP`（既定 200）: 1行の最大表示幅（超過時は末尾に`…`）
  - `APALACHE_SNIPPET_BEFORE` / `APALACHE_SNIPPET_AFTER`（既定 2/2）: エラースニペットの前後行数
- formal-aggregate.yml（PR コメントの整形）
  - `FORMAL_AGG_LINE_CLAMP`（既定 200）: コメントに表示する1行の最大幅
  - `FORMAL_AGG_ERRORS_LIMIT`（既定 5）: エラー行の最大件数
  - `FORMAL_AGG_SNIPPET_MAX_LINES`（既定 20）: エラースニペット（前後文脈を含む）の最大行数
  - コメント末尾に `Generated: <ISO8601>` を付与（生成時刻）

いずれも未設定時は既定値で動作し、非ブロッキングです。

### サンプル
- TLA+: `spec/tla/DomainSpec.tla` — 最小の不変/遷移
- Alloy: `spec/alloy/Domain.als` — 最小のアサーション

### ロードマップ（Issue #493）
- まずは非ブロッキングでラベル起動（PR 体験を阻害しない）
- 各エンジン（Conformance/Alloy/TLA+/SMT）を段階的に実配線

### CI 配線例（YAML 抜粋）
```yaml
name: Formal Verify
on:
  pull_request:
    types: [labeled, synchronize]
jobs:
  verify:
    if: contains(github.event.pull_request.labels.*.name, 'run-formal')
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - run: pnpm run verify:formal
```

### Makefile Snippet（任意）
```make
.PHONY: verify-formal
verify-formal:
	pnpm run verify:formal
```
- `artifacts/formal/formal-aggregate.json`: PR向け集約（byType/present/ranOk 等の最小情報を含む）
