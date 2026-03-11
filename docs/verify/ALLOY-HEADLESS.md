---
docRole: ssot
lastVerified: '2026-03-11'
owner: verify-first
verificationCommand: pnpm -s run check:doc-consistency
---
# Alloy Headless: Quick Reference

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

`scripts/verify/run-model-checks.mjs` で任意のヘッドレス Alloy 実行をサポートします。
- `ALLOY_JAR` を指定すると `java -jar $ALLOY_JAR <file>.als` を実行
- `ALLOY_RUN_CMD` でコマンドを上書き（`{file}`/`$ALLOY_JAR` 対応）
- 追加引数は `ALLOY_CMD_JSON`（推奨）か `ALLOY_CMD_ARGS`
- 失敗検出は `ALLOY_FAIL_REGEX` で調整、タイムアウトは `ALLOY_TIMEOUT_MS`

英語セクションに環境変数と実行例を記載しています。

This repo supports optional headless Alloy execution in `scripts/verify/run-model-checks.mjs`.

Environment variables
- `ALLOY_JAR`: path to Alloy jar. When present, the runner uses `java -jar $ALLOY_JAR <file>.als`.
- `ALLOY_RUN_CMD`: override the execution command (supports `{file}` placeholder, `$ALLOY_JAR` replacement).
- `ALLOY_CMD_JSON`: JSON array of extra args for the jar (preferred、空白や引用符に安全）。
- `ALLOY_CMD_ARGS`: 文字列引数（フォールバック）。
- `ALLOY_FAIL_REGEX`: 失敗判定の正規表現（既定: `Exception|ERROR|FAILED|Counterexample|assertion`）。
- `ALLOY_TIMEOUT_MS`: タイムアウト（既定 180000ms）。

Examples
```bash
# Minimal
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# Alloy 6 CLI (exec subcommand)
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' \
  npm run verify:model

# JSON-array args（空白/引用符を安全に扱える）
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model

# 失敗検出のチューニング + タイムアウト
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assert(ion)?' \
  ALLOY_TIMEOUT_MS=180000 \
  npm run verify:model
```

Notes
- jar を指定しない場合、`.als` の検出のみ（report-only）。
- 失敗文字列は jar/版で揺れることがあるため、`ALLOY_FAIL_REGEX` を適宜調整してください。
- `ALLOY_RUN_CMD` はシェル経由で実行されるため、信頼できる入力のみを使用してください。
