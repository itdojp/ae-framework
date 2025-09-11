# Alloy Headless: Quick Reference

This repo supports optional headless Alloy execution in `scripts/verify/run-model-checks.mjs`.

Environment variables
- `ALLOY_JAR`: path to Alloy jar. When present, the runner uses `java -jar $ALLOY_JAR <file>.als`.
- `ALLOY_CMD_JSON`: JSON array of extra args for the jar (preferred、空白や引用符に安全）。
- `ALLOY_CMD_ARGS`: 文字列引数（フォールバック）。
- `ALLOY_FAIL_REGEX`: 失敗判定の正規表現（既定: `Exception|ERROR|FAILED|Counterexample|assertion`）。
- `ALLOY_TIMEOUT_MS`: タイムアウト（既定 180000ms）。

Examples
```bash
# Minimal
ALLOY_JAR=$HOME/tools/alloy.jar npm run verify:model

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
