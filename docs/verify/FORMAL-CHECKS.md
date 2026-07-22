---
docRole: ssot
lastVerified: '2026-07-22'
owner: verify-first
verificationCommand: pnpm -s run check:doc-consistency
---
# Formal Checks: TLC/Alloy Integration (Week 1)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

CI でのフォーマル検査（TLA+/Alloy）の実行内容と成果物の場所を説明します。

- TLC (TLA+): `.github/workflows/verify.yml` の `model-check` ジョブで実行。`scripts/verify/run-model-checks.mjs` が `.tla` を探索し、`artifacts/codex/model-check.json` 等を出力（既定はレポートのみ）。
- Alloy: `.als` を検出して `model-check.json` に含めます。CI では Alloy 6 jar を取得し、`ALLOY_CMD_JSON` の argv-safe template で実行します。`ALLOY_RUN_CMD` は shell injection 防止のため無視されます。
- ローカル実行例や CI での PR サマリ内容（トレース/OK数/非OK上位など）を記載。

この直後の `English (Overview)` は簡単な概要です。より詳しい内容は、この後に続く `## English` セクションを参照してください。

## English (Overview)

This document explains where formal model checks run in CI, which artifacts are produced, and how to interpret the current report-only baseline.

- TLC (TLA+) runs in `.github/workflows/verify.yml` under the `model-check` job. `scripts/verify/run-model-checks.mjs` scans `.tla` files and writes results to `artifacts/codex/model-check.json` plus raw TLC logs under `artifacts/codex/*.tlc.log.txt`. Alloy logs are written under `artifacts/codex/*.alloy.log.txt`. Every referenced log is validated as a repository-relative, regular, non-symlink file inside this artifact root before upload and after download. The current default is report-only.
- Alloy `.als` files are detected by the same runner. CI downloads an Alloy 6 jar and executes it with the argv-safe `ALLOY_CMD_JSON` template. `ALLOY_RUN_CMD` is ignored to prevent shell-template execution.
- The PR summary reports traceability totals, TLC ok/total, and Alloy ok/total or detection-only status. Use the detailed sections below for current paths, commands, and failure interpretation.

## English

This document explains how formal model checking is executed in CI and where to find artifacts.

## What runs in CI

- TLC (TLA+) via GitHub Actions verify workflow
  - Workflow: `.github/workflows/verify.yml` (job `model-check`)
  - Tools: `actions/setup-java` + auto-download of `tla2tools.jar`
  - Runner script: `scripts/verify/run-model-checks.mjs`
  - Behavior: scans for `.tla` files under `artifacts/`, `spec/`, `docs/formal/`
  - Config resolution order (when present):
    1. `<module>.cfg` next to the `.tla`
    2. `spec/formal/configs/<module>.cfg`
    3. `spec/formal/tla+/<module>.cfg`
    4. `spec/formal/<module>.cfg`
    5. `spec/tla/<module>.cfg`
  - Output artifacts: `artifacts/codex/model-check.json`, `artifacts/codex/*.tlc.log.txt`, `artifacts/codex/*.alloy.log.txt`
  - Default: report-only (does not fail CI yet)

- Alloy (Alloy Analyzer)
  - The runner lists `.als` files and includes them in `model-check.json`
  - CI downloads an Alloy 6 jar and runs headless with argv-safe Java arguments
  - Execution can be customized with `ALLOY_JAR` / `ALLOY_CMD_JSON`; `ALLOY_RUN_CMD` is ignored
  - Optional:
    - `ALLOY_CMD_JSON`: JSON array of extra arguments (preferred, safe)
    - `ALLOY_CMD_ARGS`: whitespace‑separated extra arguments (fallback)
    - `ALLOY_FAIL_REGEX`: regex for failure detection (default: `Exception|ERROR|FAILED|Counterexample|assertion`, case‑insensitive)
    - `ALLOY_TIMEOUT_MS` (default 180000)

## Local run

```bash
# Run TLC locally (report-only):
npm run verify:model

# Optional: provide a custom TLA+ tools URL
TLA_TOOLS_URL=https://example.com/tla2tools.jar npm run verify:model

# Optional: prepare Alloy jar path and run headless
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# Extra arguments and timeout (optional)
ALLOY_JAR=$HOME/tools/alloy.jar ALLOY_CMD_ARGS="-someFlag" ALLOY_TIMEOUT_MS=180000 npm run verify:model

# Prefer JSON-array for complex arguments (quotes/spaces safe)
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model
```

## Artifacts and interpretation

- `artifacts/codex/model-check.json`
  - `status=not-run`, `ok=null` means no checker input executed and is not success evidence
  - top-level `status=tool-error`, `ok=null` means no checker completed because its tool could not start or be prepared
  - top-level `status=failed`, `ok=false` covers a completed checker failure, timeout, or mixed execution/tool failure
  - `detectedInputs`, `executedInputs`, and `skippedInputs` record input coverage; `approvedSkipRefs` is empty while reviewed skip exceptions are unsupported
  - tlc.results: execution attempts with `{ module, ok, code, log, executionStatus, evidence }`; `executionStatus=executed` means the checker process completed, while `timeout` and `tool-error` remain non-evidence outcomes
  - tlc.skipped/errors: reasons for skip/errors
  - alloy.results: execution attempts with the same status boundary; a completed checker counterexample/non-zero result is `executionStatus=executed` plus `evidence.result.status=failed`, not `tool-error`; skipped inputs remain under `alloy.skipped`
  - every result uses the closed `formal-runner-result/v1` contract with a reviewed producer binding, explicit artifact status, `verificationKind=model-check`, tool/version provenance, input, result, scope, and assumptions
  - Assurance derives claim eligibility from `verificationKind`, not the runner name. `presence`, `build`, and `typecheck` records cannot satisfy model/proof claims; current Kani presence, Lean `lake build`, and CSP typecheck therefore remain non-promoting execution records
  - SMT requires one strict `sat`/`unsat` result that matches the configured expectation; SPIN requires parsed completed-search output with zero errors, no trail/counterexample, and matching property/bounds. Exit code zero alone is not success evidence
  - each `result.logPath` and `evidence.result.logPath` must resolve under the uploaded/downloaded model-check artifact root; missing, symlink, directory, absolute, and escaping paths invalidate the report
  - `unknown`, `unspecified`, `n/a`, version/artifact-pin mismatch, and contradictory `versionStatus=verified` / `versionSource=unavailable` records preserve the attempt but are ineligible for `enforce-formal`
- `artifacts/codex/*.tlc.log.txt`: Raw TLC logs per module
- `artifacts/codex/*.alloy.log.txt`: Raw Alloy logs per spec (when executed)

### TLA modules and configs (current)

| Module | Spec path | Config path |
| --- | --- | --- |
| DomainSpec | `spec/tla/DomainSpec.tla` | `spec/tla/DomainSpec.cfg` |
| Inventory | `spec/formal/tla+/Inventory.tla` | `spec/formal/tla+/Inventory.cfg` |
| KvOnce | `spec/formal/10_abstract/KvOnce.tla` | `spec/formal/configs/KvOnce.cfg` |
| KvOnceRefinement | `spec/formal/20_refined/KvOnceRefinement.tla` | `spec/formal/configs/KvOnceRefinement.cfg` |
| KvOnceImpl | `spec/formal/30_impl/KvOnceImpl.tla` | `spec/formal/configs/KvOnceImpl.cfg` |

Note: Apalache-specific configs (`*_apalache.cfg`) are used by Apalache runs, not TLC in `verify.yml`.

### PR summary

- Posts a Verification Summary comment on PRs with:
  - Traceability totals and linked examples
  - Model Check (TLC): ok/total and top non‑OK modules
  - Alloy: ok/total (when executed) and top non‑OK specs, or “detected N specs (execution skipped)” when jar not provided
  - Optional enforcement: add PR label `enforce-formal` to require a valid report, at least one actual execution, all detected inputs executed and passing, zero tool errors/timeouts/unapproved skips, and verified tool versions (default is report-only)

### Headless Alloy examples

Run Alloy headless when you can provide a jar (or CLI):

```bash
# Minimal
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# With JSON-array args (quotes/spaces safe)
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model

# With regex tuning and timeout
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assert(ion)?' \
  ALLOY_TIMEOUT_MS=180000 \
  npm run verify:model
```


## Next steps

- Gate failures on model checking (opt-in label or directory presence)
- Implement headless Alloy execution (jar/CLI options) with timeouts
- Post PR comments summarizing formal results (green/red + links)

## Notes

- If `ALLOY_JAR` is not set, Alloy execution is skipped (detection only). Provide the jar path for headless runs.
- The runner treats non-zero checker results and timeouts as failures; a process that completed with a non-zero checker result is still recorded as an executed checker (`outcome=fail`), while spawn/preparation failures are `tool-error`. Logs are saved under `artifacts/codex/*.alloy.log.txt`.

## First checks after CI

- Open `artifacts/codex/model-check.json` first and confirm whether the run produced `tlc.results`, `tlc.skipped`, `alloy.results`, or `alloy.errors`.
- If TLC looks suspicious, inspect the corresponding `artifacts/codex/*.tlc.log.txt` files before changing the config resolution order.
- If Alloy is listed as detected-only, verify whether `ALLOY_JAR` or `ALLOY_RUN_CMD` was intentionally omitted.
- When the PR summary shows non-OK modules/specs, use those names as the entry point for raw log inspection instead of scanning the entire artifact directory.

## Failure pattern guidance (Alloy)

Different Alloy jars may emit different failure strings. You can tune `ALLOY_FAIL_REGEX` as needed.

Common patterns:

- `Exception` – any unhandled exceptions
- `ERROR` – generic error prefix
- `FAILED` – assertion/check failure markers
- `Counterexample` – counterexample found for an assertion
- `assertion` – assertion-related lines (some jars include lowercase)

Combine with `|` to build a case-insensitive regex. Example:

```
ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assertion'
```

Jar/version specific notes (examples, adjust as needed):

- Some builds emit `Counterexample found.
  Assertion XYZ is invalid` for failing `assert` blocks.
- Others use `FAILED` preceded by the assertion name or a check ID.
- Parser-level issues often include `Exception` or `ERROR` with a stack trace.

Tip: Start with the default and add the most common markers seen in your CI logs. Keep the regex concise to avoid false positives.

### Regex presets (examples)

Use one of these as a starting point via `ALLOY_FAIL_REGEX`.

- Default (balanced):
  - `Exception|ERROR|FAILED|Counterexample|assertion`
- Strict (catch more noise, may include false positives):
  - `Exception|ERROR|FAILED|FATAL|SEVERE|Counterexample|assert(ion)?|Traceback`
- Permissive (only clear assertion/counterexample failures):
  - `FAILED|Counterexample|assert(ion)?`
- Jar variant A (counterexample phrasing):
  - `Counterexample found|Assertion .* is invalid|FAILED`
- Parser-heavy (catch parse/semantic issues):
  - `Exception|ERROR|Parse|Lexer|Stack trace|Traceback`

Export example in CI or local shell:

```
ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assertion' npm run verify:model
```

---

## 日本語

このドキュメントは、CI におけるフォーマルモデル検査（TLA+/Alloy）の実行と、成果物の場所・解釈方法を説明します。

### CI で実行される内容

- TLC (TLA+)
  - ワークフロー: `.github/workflows/verify.yml`（ジョブ `model-check`）
  - 使用ツール: `actions/setup-java` + `tla2tools.jar` 自動取得
  - ランナー: `scripts/verify/run-model-checks.mjs`
  - 動作: `artifacts/`, `spec/`, `docs/formal/` 配下の `.tla` を走査
  - 出力: `artifacts/codex/model-check.json`, `artifacts/codex/*.tlc.log.txt`
  - 既定: レポートのみ（CI を失敗させない）

- Alloy (Alloy Analyzer)
  - `.als` を検出し `model-check.json` に含める
  - `ALLOY_JAR` を与えた場合にヘッドレス実行（`java -jar $ALLOY_JAR {file}`）
  - オプション環境変数:
    - `ALLOY_CMD_JSON`: 追加引数（JSON 配列; 空白/引用に安全）
    - `ALLOY_CMD_ARGS`: 追加引数（文字列; フォールバック）
    - `ALLOY_FAIL_REGEX`: 失敗判定用の正規表現（既定 `Exception|ERROR|FAILED|Counterexample|assertion`）
    - `ALLOY_TIMEOUT_MS`: タイムアウト（既定 180000）

### ローカル実行

```bash
# TLC（報告のみ）
npm run verify:model

# TLA+ ツール URL を指定
TLA_TOOLS_URL=https://example.com/tla2tools.jar npm run verify:model

# Alloy jar を指定してヘッドレス実行
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# 追加引数/タイムアウト
ALLOY_JAR=$HOME/tools/alloy.jar ALLOY_CMD_ARGS="-someFlag" ALLOY_TIMEOUT_MS=180000 npm run verify:model

# 複雑な引数は JSON 配列を推奨
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model
```

### 成果物と読み方

- `artifacts/codex/model-check.json`
  - `detectedInputs` / `executedInputs` / `skippedInputs` で input coverage を記録し、review 済み skip exception 未対応の間は `approvedSkipRefs=[]` とする
  - `tlc.results`: `{ module, ok, code, log, executionStatus, evidence }` の配列
  - `tlc.skipped/errors`: スキップ/エラーの理由。timeout/tool-error と skip は別 outcome として保持する
  - `alloy.results/skipped/errors`: 同じ execution boundary と検出・準備状況
  - `evidence` は closed `formal-runner-result/v1`、review 済み producer binding、明示 artifact status、tool/version/input/result/scope/assumptions を要求する。version の unknown/mismatch と矛盾する `versionStatus=verified` / `versionSource=unavailable` は attempt を残すが enforcement evidence にはしない
- `artifacts/codex/*.tlc.log.txt`: TLC の生ログ（モジュールごと）
- `artifacts/codex/*.alloy.log.txt`: Alloy の生ログ（実行した場合）

### TLA モジュールと cfg（現行）

| モジュール | Spec パス | cfg パス |
| --- | --- | --- |
| DomainSpec | `spec/tla/DomainSpec.tla` | `spec/tla/DomainSpec.cfg` |
| Inventory | `spec/formal/tla+/Inventory.tla` | `spec/formal/tla+/Inventory.cfg` |
| KvOnce | `spec/formal/10_abstract/KvOnce.tla` | `spec/formal/configs/KvOnce.cfg` |
| KvOnceRefinement | `spec/formal/20_refined/KvOnceRefinement.tla` | `spec/formal/configs/KvOnceRefinement.cfg` |
| KvOnceImpl | `spec/formal/30_impl/KvOnceImpl.tla` | `spec/formal/configs/KvOnceImpl.cfg` |

※ Apalache 用の `*_apalache.cfg` は Apalache 実行に使用し、TLC では使用しません。

### PR サマリ

PR に検証サマリを投稿します:
- トレーサビリティ合計とリンク例
- モデル検査 (TLC): ok/total と非 OK モジュール上位
- Alloy: ok/total（実行時）と非 OK スペック上位、または jar 未指定時の検出数
- 任意の強制: ラベル `enforce-formal` を付けると、valid report、1件以上の actual execution、検出 input 全件の実行・成功、tool error/timeout/未承認 skip が0件、verified tool version を要求する（既定はレポートのみ）

### ヘッドレス Alloy 実行例

```bash
# 最小
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# Alloy 6 CLI (exec) を使う場合
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' \
  npm run verify:model

# JSON 配列の引数（空白/引用に強い）
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model

# 失敗検出のチューニング + タイムアウト
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assert(ion)?' \
  ALLOY_TIMEOUT_MS=180000 \
  npm run verify:model
```

### 次のステップ

- モデル検査結果で失敗をゲート（ラベルやディレクトリ存在で opt-in）
- ヘッドレス Alloy 実行（jar/CLI + タイムアウト制御）の整備
- PR コメントに緑/赤とリンクを掲載

### 備考

- `ALLOY_JAR` が未設定の場合、Alloy 実行はスキップ（検出のみ）。jar を設定するとヘッドレス実行
- 非ゼロ終了やタイムアウトは失敗扱い。ログは `artifacts/codex/*.alloy.log.txt` に保存

### CI 実行後に最初に確認する項目

- まず `artifacts/codex/model-check.json` を開き、`tlc.results`、`tlc.skipped`、`alloy.results`、`alloy.errors` のどこに結果が出ているかを確認する
- TLC が怪しい場合は、設定ファイル探索順を変える前に対応する `artifacts/codex/*.tlc.log.txt` を確認する
- Alloy が検出のみになっている場合は、`ALLOY_JAR` または `ALLOY_RUN_CMD` を意図的に省略していないか確認する
- PR サマリで non-OK の module/spec が出ている場合は、その名前を起点に raw log を辿り、`summary.totalViolations == 0` のみで判断しない

### 失敗パターン（Alloy）

Alloy の jar によりエラーメッセージは異なることがあります。`ALLOY_FAIL_REGEX` を状況に合わせて調整してください。

一般的なパターン:
- `Exception`（未処理の例外）
- `ERROR`（一般的なエラー）
- `FAILED`（アサーション/チェックの失敗）
- `Counterexample`（反例の検出）
- `assertion`（アサーション関連行）

例（CI/ローカル）:
```bash
ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assertion' npm run verify:model
```
