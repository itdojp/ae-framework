---
docRole: ssot
lastVerified: '2026-03-29'
owner: verify-first
verificationCommand: pnpm -s run check:doc-consistency
---
# Alloy Headless: Quick Reference

> 🌍 Language / 言語: English | 日本語

---

## English

This repository supports optional headless Alloy execution in `scripts/verify/run-model-checks.mjs`.

### Environment variables

- `ALLOY_JAR`: path to the Alloy jar. When present, the runner uses `java -jar $ALLOY_JAR <file>.als`.
- `ALLOY_RUN_CMD`: overrides the execution command. Supports the `{file}` placeholder and `$ALLOY_JAR` replacement.
- `ALLOY_CMD_JSON`: JSON array of extra args for the jar. Preferred because it is safe for spaces and quotes.
- `ALLOY_CMD_ARGS`: string-form extra args. Fallback only.
- `ALLOY_FAIL_REGEX`: regex used to decide failure (`Exception|ERROR|FAILED|Counterexample|assertion` by default).
- `ALLOY_TIMEOUT_MS`: timeout in milliseconds (`180000` by default).

### Examples

```bash
# Minimal
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# Alloy 6 CLI (exec subcommand)
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' \
  npm run verify:model

# JSON-array args (safe for spaces and quotes)
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model

# Tune failure detection + timeout
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assert(ion)?' \
  ALLOY_TIMEOUT_MS=180000 \
  npm run verify:model
```

### Notes

- If no jar is provided, the workflow only detects `.als` files and stays report-only.
- Failure strings vary by jar version and invocation mode, so adjust `ALLOY_FAIL_REGEX` when needed.
- `ALLOY_RUN_CMD` is executed through the shell. Use trusted input only.

## 日本語

このリポジトリでは、`scripts/verify/run-model-checks.mjs` で optional な headless Alloy 実行をサポートします。

### 環境変数

- `ALLOY_JAR`: Alloy jar のパスです。指定すると runner は `java -jar $ALLOY_JAR <file>.als` を使います。
- `ALLOY_RUN_CMD`: 実行コマンドを上書きします。`{file}` プレースホルダと `$ALLOY_JAR` 置換をサポートします。
- `ALLOY_CMD_JSON`: jar に渡す追加引数の JSON 配列です。空白や引用符に安全なため、こちらを推奨します。
- `ALLOY_CMD_ARGS`: 文字列形式の追加引数です。フォールバック用です。
- `ALLOY_FAIL_REGEX`: failure 判定に使う正規表現です。既定値は `Exception|ERROR|FAILED|Counterexample|assertion` です。
- `ALLOY_TIMEOUT_MS`: ミリ秒単位のタイムアウトです。既定値は `180000` です。

### 実行例

```bash
# Minimal
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

# Alloy 6 CLI (exec subcommand)
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' \
  npm run verify:model

# JSON-array args（空白や引用符を安全に扱える）
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_CMD_JSON='["-someFlag","--opt","value with spaces"]' \
  npm run verify:model

# failure 判定とタイムアウトの調整
ALLOY_JAR=$HOME/tools/alloy.jar \
  ALLOY_FAIL_REGEX='Exception|ERROR|FAILED|Counterexample|assert(ion)?' \
  ALLOY_TIMEOUT_MS=180000 \
  npm run verify:model
```

### 注意事項

- jar を指定しない場合、workflow は `.als` の存在確認だけを行い、report-only のままです。
- failure 文字列は jar の版や起動方法で揺れるため、必要に応じて `ALLOY_FAIL_REGEX` を調整してください。
- `ALLOY_RUN_CMD` は shell 経由で実行されるため、信頼できる入力だけを使ってください。
