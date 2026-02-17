# Automation Profiles（PR自動化プロファイル）

PR自動化（Copilot Review Gate / Copilot Auto Fix / Auto Merge）の設定を、Repository Variables 1つで段階的に切り替えるための運用ガイドです。

一次情報:
- `scripts/ci/lib/automation-config.mjs`
- `.github/workflows/copilot-auto-fix.yml`
- `.github/workflows/copilot-review-gate.yml`
- `.github/workflows/pr-ci-status-comment.yml`

## 1. 使い方

Repository Variables に `AE_AUTOMATION_PROFILE` を設定します。

- `conservative`
- `balanced`
- `aggressive`

未設定時はプロファイル無効で、既存の個別変数（`AE_COPILOT_AUTO_FIX*`, `AE_AUTO_MERGE*`, `AE_GH_*`, `AE_AUTOMATION_GLOBAL_DISABLE` など）がそのまま使われます。

## 2. 優先順位

設定の解決順は次のとおりです。

1. 個別変数（明示設定）
2. `AE_AUTOMATION_PROFILE` のプリセット値
3. スクリプトの既定値

つまり、プロファイルを有効化していても、個別変数を指定すればその値が優先されます。

文字列系の個別変数（例: `AE_COPILOT_AUTO_FIX_LABEL`, `AE_AUTO_MERGE_LABEL`）を明示的に空文字へ上書きしたい場合は、`(empty)` を設定します。

## 3. プロファイル内容

| Key | conservative | balanced | aggressive |
| --- | --- | --- | --- |
| `AE_AUTOMATION_GLOBAL_DISABLE` | `0` | `0` | `0` |
| `AE_COPILOT_AUTO_FIX` | `1` | `1` | `1` |
| `AE_COPILOT_AUTO_FIX_SCOPE` | `docs` | `docs` | `all` |
| `AE_COPILOT_AUTO_FIX_LABEL` | `copilot-auto-fix` | *(empty)* | *(empty)* |
| `AE_AUTO_MERGE` | `1` | `1` | `1` |
| `AE_AUTO_MERGE_MODE` | `label` | `label` | `all` |
| `AE_AUTO_MERGE_LABEL` | `auto-merge` | `auto-merge` | *(empty)* |
| `AE_GH_THROTTLE_MS` | `400` | `300` | `150` |
| `AE_GH_RETRY_MAX_ATTEMPTS` | `10` | `8` | `6` |
| `AE_GH_RETRY_INITIAL_DELAY_MS` | `1000` | `750` | `500` |
| `AE_GH_RETRY_MAX_DELAY_MS` | `120000` | `60000` | `30000` |
| `AE_GH_RETRY_MULTIPLIER` | `2` | `2` | `2` |
| `AE_GH_RETRY_JITTER_MS` | `400` | `250` | `100` |
| `COPILOT_REVIEW_WAIT_MINUTES` | `7` | `5` | `2` |
| `COPILOT_REVIEW_MAX_ATTEMPTS` | `4` | `3` | `2` |

## 4. 推奨導入順

1. `conservative`（docs + label opt-in）
2. `balanced`（docs + label opt-in、遅延調整をやや緩和）
3. `aggressive`（all + auto-merge all）

## 5. 可観測性

各 workflow で `automation-config.mjs` を実行し、次を出力します。

- `GITHUB_ENV` への解決済み値
- `GITHUB_STEP_SUMMARY` への設定サマリ（Key/Value/Source）

これにより「どの値がどこから採用されたか」を run ごとに追跡できます。

## 6. 注意点

- `AE_AUTO_MERGE_MODE=label` で `AE_AUTO_MERGE_LABEL` が空の場合は警告します。
- `AE_GH_RETRY_MAX_DELAY_MS < AE_GH_RETRY_INITIAL_DELAY_MS` の場合は、`MAX_DELAY` を `INITIAL_DELAY` に補正します。
- プロファイル名が不正な場合は無効扱い（既定値にフォールバック）です。
- `AE_AUTOMATION_GLOBAL_DISABLE=1`（`true` / `yes` / `on` も可）の場合、auto-fix / auto-merge / update-branch / self-heal / autopilot の実行は安全側で停止（skip）します。
