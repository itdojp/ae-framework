---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Automation Profiles（PR自動化プロファイル）

PR自動化（Copilot Review Gate / Copilot Auto Fix / Auto Merge / Policy Gate）の設定を、Repository Variables 1つで段階的に切り替えるための運用ガイドです。

> Language / 言語: English | 日本語

## English

This guide explains how to roll PR automation settings (Copilot Review Gate, Copilot Auto Fix, Auto Merge, and Policy Gate) forward in stages by setting a single Repository Variable.

Primary sources:
- `scripts/ci/lib/automation-config.mjs`
- `.github/workflows/copilot-auto-fix.yml`
- `.github/workflows/copilot-review-gate.yml`
- `.github/workflows/pr-ci-status-comment.yml`
- `.github/workflows/policy-gate.yml`
- `.github/workflows/codex-autopilot-lane.yml`

### 1. How to use it

Set `AE_AUTOMATION_PROFILE` in Repository Variables.

- `conservative`
- `balanced`
- `aggressive`

If the variable is unset, the profile layer is disabled and the existing explicit variables stay in effect as-is, including:

- `AI_REVIEW_ACTORS`
- `AE_COPILOT_AUTO_FIX*`
- `AE_AUTO_MERGE*`
- `AE_GH_*`
- `AE_AUTOMATION_GLOBAL_DISABLE`
- `AE_REVIEW_TOPOLOGY`
- `AE_POLICY_MIN_HUMAN_APPROVALS`
- `AE_AUTOPILOT_AUTO_LABEL`
- `AE_AUTOPILOT_RISK_POLICY_PATH`
- `AE_AUTO_MERGE_REQUIRE_RISK_LOW`
- `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE`

Notes:
- reviewer actors prefer `AI_REVIEW_ACTORS`; when it is unset, the implementation falls back to `COPILOT_ACTORS` for backward compatibility
- `AE_REVIEW_TOPOLOGY` and `AE_POLICY_MIN_HUMAN_APPROVALS` are effective only in versions where both `automation-config` and `policy-gate` support them

### 2. Precedence

Configuration is resolved in this order:

1. explicit per-variable settings
2. values supplied by `AE_AUTOMATION_PROFILE`
3. script defaults

That means explicit variables override the profile even when the profile is enabled.

If an operator needs to override a string variable to an explicit empty value (for example, `AE_COPILOT_AUTO_FIX_LABEL` or `AE_AUTO_MERGE_LABEL`), set the repository variable to `(empty)`.

### 3. Profile contents

| Key | conservative | balanced | aggressive |
| --- | --- | --- | --- |
| `AE_REVIEW_TOPOLOGY` | `team` | `team` | `team` |
| `AE_POLICY_MIN_HUMAN_APPROVALS` | *(empty)* | *(empty)* | *(empty)* |
| `AE_AUTOMATION_GLOBAL_DISABLE` | `0` | `0` | `0` |
| `AE_COPILOT_AUTO_FIX` | `1` | `1` | `1` |
| `AE_COPILOT_AUTO_FIX_SCOPE` | `docs` | `docs` | `all` |
| `AE_COPILOT_AUTO_FIX_LABEL` | `copilot-auto-fix` | *(empty)* | *(empty)* |
| `AE_AUTO_MERGE` | `1` | `1` | `1` |
| `AE_AUTO_MERGE_MODE` | `label` | `label` | `all` |
| `AE_AUTO_MERGE_LABEL` | `auto-merge` | `auto-merge` | *(empty)* |
| `AE_AUTO_MERGE_REQUIRE_RISK_LOW` | `1` | `1` | `1` |
| `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE` | `1` | `1` | `1` |
| `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN` | `1` | `1` | `1` |
| `AE_GH_THROTTLE_MS` | `400` | `300` | `150` |
| `AE_GH_RETRY_MAX_ATTEMPTS` | `10` | `8` | `6` |
| `AE_GH_RETRY_INITIAL_DELAY_MS` | `1000` | `750` | `500` |
| `AE_GH_RETRY_MAX_DELAY_MS` | `120000` | `60000` | `30000` |
| `AE_GH_RETRY_MULTIPLIER` | `2` | `2` | `2` |
| `AE_GH_RETRY_JITTER_MS` | `400` | `250` | `100` |
| `COPILOT_REVIEW_WAIT_MINUTES` | `7` | `5` | `2` |
| `COPILOT_REVIEW_MAX_ATTEMPTS` | `4` | `3` | `2` |

Representative values that do not change by profile and continue to resolve from defaults or explicit values:

- `AI_REVIEW_ACTORS`
- `AE_AUTOPILOT_AUTO_LABEL`
- `AE_AUTOPILOT_RISK_POLICY_PATH`

Default actors for `AI_REVIEW_ACTORS` when it is unset:

- `copilot-pull-request-reviewer`
- `github-copilot`
- `github-copilot[bot]`
- `copilot`
- `copilot[bot]`
- `chatgpt-codex-connector`
- `chatgpt-codex-connector[bot]`
- `Copilot`

### 4. Recommended rollout order

1. `conservative` (docs + label opt-in)
2. `balanced` (docs + label opt-in with lighter retry delays)
3. `aggressive` (all scope + auto-merge all)

### 5. Observability

Each workflow executes `automation-config.mjs` and emits:

- resolved values into `GITHUB_ENV`
- a configuration summary into `GITHUB_STEP_SUMMARY` including key, value, and source

This lets operators trace which value was selected from which source for each run.

### 6. Cautions

- warn when `AE_AUTO_MERGE_MODE=label` but `AE_AUTO_MERGE_LABEL` is empty
- if `AE_GH_RETRY_MAX_DELAY_MS < AE_GH_RETRY_INITIAL_DELAY_MS`, clamp `MAX_DELAY` up to `INITIAL_DELAY`
- treat invalid profile names as disabled and fall back to defaults
- when `AE_AUTOMATION_GLOBAL_DISABLE=1` (also `true` / `yes` / `on`), stop update-oriented lanes on the safe side: auto-fix, auto-merge, update-branch, self-heal, and autopilot
- `AE_AUTOPILOT_ACTIONABLE_COMMAND`, `AE_AUTOPILOT_ACTIONABLE_DRY_RUN`, `AE_AUTOPILOT_MAX_ROUNDS`, and `AE_AUTOPILOT_ROUND_WAIT_*` are outside `automation-config` management and are therefore not changed by the profile

## 日本語

一次情報:
- `scripts/ci/lib/automation-config.mjs`
- `.github/workflows/copilot-auto-fix.yml`
- `.github/workflows/copilot-review-gate.yml`
- `.github/workflows/pr-ci-status-comment.yml`
- `.github/workflows/policy-gate.yml`
- `.github/workflows/codex-autopilot-lane.yml`

## 1. 使い方

Repository Variables に `AE_AUTOMATION_PROFILE` を設定します。

- `conservative`
- `balanced`
- `aggressive`

未設定時はプロファイル無効で、既存の個別変数（`AI_REVIEW_ACTORS`, `AE_COPILOT_AUTO_FIX*`, `AE_AUTO_MERGE*`, `AE_GH_*`, `AE_AUTOMATION_GLOBAL_DISABLE`, `AE_REVIEW_TOPOLOGY`, `AE_POLICY_MIN_HUMAN_APPROVALS`, `AE_AUTOPILOT_AUTO_LABEL`, `AE_AUTOPILOT_RISK_POLICY_PATH` など）がそのまま使われます（`AE_AUTO_MERGE_REQUIRE_RISK_LOW` / `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE` を含む）。

補足:
- reviewer actor は `AI_REVIEW_ACTORS` が優先され、未設定時は `COPILOT_ACTORS` を後方互換で参照します。

注記:
- `AE_REVIEW_TOPOLOGY` / `AE_POLICY_MIN_HUMAN_APPROVALS` は、automation-config と policy-gate の対応実装が入っているバージョンで有効です。

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
| `AE_REVIEW_TOPOLOGY` | `team` | `team` | `team` |
| `AE_POLICY_MIN_HUMAN_APPROVALS` | *(empty)* | *(empty)* | *(empty)* |
| `AE_AUTOMATION_GLOBAL_DISABLE` | `0` | `0` | `0` |
| `AE_COPILOT_AUTO_FIX` | `1` | `1` | `1` |
| `AE_COPILOT_AUTO_FIX_SCOPE` | `docs` | `docs` | `all` |
| `AE_COPILOT_AUTO_FIX_LABEL` | `copilot-auto-fix` | *(empty)* | *(empty)* |
| `AE_AUTO_MERGE` | `1` | `1` | `1` |
| `AE_AUTO_MERGE_MODE` | `label` | `label` | `all` |
| `AE_AUTO_MERGE_LABEL` | `auto-merge` | `auto-merge` | *(empty)* |
| `AE_AUTO_MERGE_REQUIRE_RISK_LOW` | `1` | `1` | `1` |
| `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE` | `1` | `1` | `1` |
| `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN` | `1` | `1` | `1` |
| `AE_GH_THROTTLE_MS` | `400` | `300` | `150` |
| `AE_GH_RETRY_MAX_ATTEMPTS` | `10` | `8` | `6` |
| `AE_GH_RETRY_INITIAL_DELAY_MS` | `1000` | `750` | `500` |
| `AE_GH_RETRY_MAX_DELAY_MS` | `120000` | `60000` | `30000` |
| `AE_GH_RETRY_MULTIPLIER` | `2` | `2` | `2` |
| `AE_GH_RETRY_JITTER_MS` | `400` | `250` | `100` |
| `COPILOT_REVIEW_WAIT_MINUTES` | `7` | `5` | `2` |
| `COPILOT_REVIEW_MAX_ATTEMPTS` | `4` | `3` | `2` |

profile で値が変化しない（`default` または `explicit`/`legacy` で決まる）代表項目:
- `AI_REVIEW_ACTORS`
- `AE_AUTOPILOT_AUTO_LABEL`
- `AE_AUTOPILOT_RISK_POLICY_PATH`

`AI_REVIEW_ACTORS` の default actors（未設定時）:
- `copilot-pull-request-reviewer`
- `github-copilot`
- `github-copilot[bot]`
- `copilot`
- `copilot[bot]`
- `chatgpt-codex-connector`
- `chatgpt-codex-connector[bot]`
- `Copilot`

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
- `AE_AUTOPILOT_ACTIONABLE_COMMAND` / `AE_AUTOPILOT_ACTIONABLE_DRY_RUN` / `AE_AUTOPILOT_MAX_ROUNDS` / `AE_AUTOPILOT_ROUND_WAIT_*` は `automation-config` 管理外のため、プロファイルでは変更されません。
