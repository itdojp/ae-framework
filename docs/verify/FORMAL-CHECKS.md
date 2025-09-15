# Formal Checks: TLC/Alloy Integration (Week 1)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

CI でのフォーマル検査（TLA+/Alloy）の実行内容と成果物の場所を説明します。

- TLC (TLA+): `.github/workflows/verify.yml` の `model-check` ジョブで実行。`scripts/verify/run-model-checks.mjs` が `.tla` を探索し、`artifacts/codex/model-check.json` 等を出力（既定はレポートのみ）。
- Alloy: `.als` を検出して `model-check.json` に含めます。`ALLOY_JAR` 指定時にヘッドレス実行が可能（タイムアウト/失敗検出を環境変数で調整）。
- ローカル実行例や CI での PR サマリ内容（トレース/OK数/非OK上位など）を記載。

詳細は以下の英語セクションを参照してください。

## English

This document explains how formal model checking is executed in CI and where to find artifacts.

## What runs in CI

- TLC (TLA+) via GitHub Actions verify workflow
  - Workflow: `.github/workflows/verify.yml` (job `model-check`)
  - Tools: `actions/setup-java` + auto-download of `tla2tools.jar`
  - Runner script: `scripts/verify/run-model-checks.mjs`
  - Behavior: scans for `.tla` files under `artifacts/`, `specs/`, `docs/formal/`
  - Output artifacts: `artifacts/codex/model-check.json`, `artifacts/codex/*.tlc.log.txt`
  - Default: report-only (does not fail CI yet)

- Alloy (Alloy Analyzer): scaffolded detection
  - The runner lists `.als` files and includes them in `model-check.json`
  - Execution (headless) is supported when `ALLOY_JAR` is provided (safe default: `java -jar $ALLOY_JAR {file}`)
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
  - tlc.results: array of `{ module, ok, code, log }`
  - tlc.skipped/errors: reasons for skip/errors
  - alloy.results/skipped/errors: detection and readiness info
- `artifacts/codex/*.tlc.log.txt`: Raw TLC logs per module
- `artifacts/codex/*.alloy.log.txt`: Raw Alloy logs per spec (when executed)

### PR summary

- Posts a Verification Summary comment on PRs with:
  - Traceability totals and linked examples
  - Model Check (TLC): ok/total and top non‑OK modules
  - Alloy: ok/total (when executed) and top non‑OK specs, or “detected N specs (execution skipped)” when jar not provided
  - Optional enforcement: add PR label `enforce-formal` to fail the PR when TLC/Alloy has failures (default is report-only)

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
# Notes

- If `ALLOY_JAR` is not set, Alloy execution is skipped (detection only). Provide the jar path for headless runs.
- The runner treats non-zero exit or timeouts as failures; logs are saved under `artifacts/codex/*.alloy.log.txt`.

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
  - 動作: `artifacts/`, `specs/`, `docs/formal/` 配下の `.tla` を走査
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
  - `tlc.results`: `{ module, ok, code, log }` の配列
  - `tlc.skipped/errors`: スキップ/エラーの理由
  - `alloy.results/skipped/errors`: 検出・準備状況
- `artifacts/codex/*.tlc.log.txt`: TLC の生ログ（モジュールごと）
- `artifacts/codex/*.alloy.log.txt`: Alloy の生ログ（実行した場合）

### PR サマリ

PR に検証サマリを投稿します:
- トレーサビリティ合計とリンク例
- モデル検査 (TLC): ok/total と非 OK モジュール上位
- Alloy: ok/total（実行時）と非 OK スペック上位、または jar 未指定時の検出数
- 任意の強制: ラベル `enforce-formal` を付けると TLC/Alloy 失敗で PR を失敗（既定はレポートのみ）

### ヘッドレス Alloy 実行例

```bash
# 最小
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

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
