---
docRole: ssot
lastVerified: '2026-03-23'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Opt-in Controls Catalog（ラベル / Slash / dispatch）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
This document is the operational catalog for opt-in controls that trigger heavier CI work or change gate behavior while keeping default PR cost lower.

Primary sources:
- `.github/workflows/agent-commands.yml`
- `.github/workflows/verify-lite.yml`
- `.github/workflows/slash-commands.yml`

### 2. Scope
- PR-side controls: labels and slash commands on PR comments
- Issue-side controls: slash commands on issue comments

### 3. Representative PR labels

| Label | Effect | Main workflow / job | Notes |
| --- | --- | --- | --- |
| `run-qa` | mark QA-equivalent steps for the next eligible PR event | `ae-ci.yml` | `/run-qa` adds the label; use `/run-qa-dispatch` for immediate execution |
| `run-security` | mark security / SBOM flows for the next eligible PR event | `security.yml`, `sbom-generation.yml`, `cedar-quality-gates.yml` | `/run-security` adds the label only; fork PRs remain restricted |
| `run-cedar` | mark Cedar quality gates for the next eligible PR event | `cedar-quality-gates.yml` | `/run-cedar` adds the label; `/run-cedar-dispatch` runs immediately |
| `run-formal` | enable formal verification on the next `verify-lite` execution | `verify-lite.yml` step `Run formal` | label-gated inside verify-lite; use `/formal-verify-dispatch` for manual execution |
| `run-resilience` | enable resilience quick checks on the next `verify-lite` execution | `verify-lite.yml` step `Resilience quick` | `/run-resilience` adds the label only |
| `run-hermetic` | mark hermetic CI for the next eligible PR event | `ci.yml`, `hermetic-ci.yml` | `/run-hermetic` adds the label; use a dispatch path for immediate execution |
| `run-spec` | record intent for fail-fast spec validation | `spec-validation.yml` | `/run-spec` adds an informational label only; use `/spec-validation-dispatch` for actual execution |
| `run-trace` | re-evaluate KvOnce trace validation as required-gate evidence | `spec-generate-model.yml` (`trace-conformance`, `KvOnce Trace Validation`) | label only in the current repository |
| `run-drift` | run codegen drift detection | `codegen-drift-check.yml` | attached by `/run-drift` |
| `enforce-assurance` | make assurance summary blocking | `verify-lite.yml` strict assurance step | recommended only for high-risk PRs |
| `enforce-bdd-lint` | make BDD lint blocking | `verify-lite.yml` | attached by `/enforce-bdd-lint` |
| `enforce-verify-lite-lint` | enforce verify-lite lint baseline | `verify-lite.yml` | PR label only |
| `enforce-context-pack` | make Context Pack E2E blocking | `context-pack-quality-gate.yml` | used during staged rollout |
| `enforce-discovery` | make Discovery Pack validate/compile blocking | `verify-lite.yml` Discovery rollout | report-only by default |
| `ci-non-blocking` | mark selected jobs non-blocking | workflow `continue-on-error` branches | attached by `/non-blocking` |
| `enforce-coverage` | require coverage gate | `coverage-check.yml` | attached by `/enforce-coverage` |
| `coverage:<pct>` | override coverage threshold | `coverage-check.yml` | for example `/coverage 75` |
| `pr-summary:digest` | record legacy digest intent only | `pr-ci-status-comment.yml` | `/pr-digest` adds a compatibility label, but current rendering is concise by default when `pr-summary:detailed` is absent |
| `pr-summary:detailed` | switch PR summary to detailed mode on the next maintenance cycle | `pr-ci-status-comment.yml` | attached by `/pr-detailed`; current renderer checks only this label |
| `autopilot:on` | opt in to Codex Autopilot Lane | `codex-autopilot-lane.yml` | touchless merge opt-in |

Operational note:
- PR automation itself is usually enabled through Repository Variables rather than labels.

### 4. Repository Variables used with opt-in automation

#### 4.1 Core automation variables

| Variable | Role | Default | Reference |
| --- | --- | --- | --- |
| `AE_AUTOMATION_PROFILE` | bundled PR automation profile (`conservative` / `balanced` / `aggressive`) | unset (disabled) | `docs/ci/automation-profiles.md` |
| `AE_REVIEW_TOPOLOGY` | approval topology (`team` / `solo`) | `team` | `docs/ci/pr-automation.md` |
| `AE_POLICY_MIN_HUMAN_APPROVALS` | explicit human-approval override for policy-gate | unset | `docs/ci/pr-automation.md` |
| `AE_POLICY_ENGINE_MODE` | policy shadow compare mode (`shadow` / `shadow_strict`) | `shadow` | `docs/ci/pr-automation.md` |
| `AE_COPILOT_AUTO_FIX` | enable Copilot suggestion auto-apply | unset (off) | `docs/ci/copilot-auto-fix.md` |
| `AE_COPILOT_AUTO_FIX_SCOPE` | auto-fix scope (`docs` / `all`) | `docs` | `docs/ci/copilot-auto-fix.md` |
| `AE_COPILOT_AUTO_FIX_LABEL` | optional label gate for auto-fix | unset | `docs/ci/copilot-auto-fix.md` |
| `AE_AUTO_MERGE` | enable automatic merge activation | unset (off) | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_MODE` | auto-merge mode (`all` / `label`) | `all` | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_LABEL` | opt-in label in `label` mode | unset | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_REQUIRE_RISK_LOW` | require `risk:low` for auto-merge (`1` / `0`) | `1` | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE` | require Change Package Validation summary (`1` / `0`) | `1` | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN` | allow `WARN` from Change Package Validation (`1` / `0`) | `1` | `docs/ci/auto-merge.md` |

Notes:
- Explicit variables override `AE_AUTOMATION_PROFILE`.
- These settings are repository-level rollout controls, not per-PR labels.

#### 4.2 GitHub API throttling variables
Use these only when GitHub API rate limiting or secondary throttling becomes operationally relevant.

| Variable | Role | Default |
| --- | --- | --- |
| `AE_GH_THROTTLE_MS` | minimum interval between `gh` calls | `250` (`0` disables) |
| `AE_GH_RETRY_MAX_ATTEMPTS` | max attempt count including the first call | `8` |
| `AE_GH_RETRY_INITIAL_DELAY_MS` | initial retry delay | `750` |
| `AE_GH_RETRY_MAX_DELAY_MS` | maximum retry delay | `60000` |
| `AE_GH_RETRY_MULTIPLIER` | exponential retry multiplier | `2` |
| `AE_GH_RETRY_JITTER_MS` | retry jitter cap | `250` |
| `AE_GH_RETRY_DEBUG` | enable retry debug logging | unset |

#### 4.3 Self-heal and autopilot variables
Representative variables for follow-on automation:

| Variable | Role | Default | Reference |
| --- | --- | --- | --- |
| `AE_SELF_HEAL_ENABLED` | enable PR self-heal workflow | unset (off) | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_MAX_ROUNDS` | max recovery rounds per PR | `3` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_MAX_AGE_MINUTES` | max age of failed checks eligible for rerun | `180` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_MAX_PRS` | max PRs per scheduled run | `20` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_ROUND_WAIT_SECONDS` | wait between self-heal rounds | `60` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_WAIT_STRATEGY` | wait strategy (`fixed` / `exponential`) | `fixed` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_ROUND_WAIT_MAX_SECONDS` | max exponential wait | `AE_SELF_HEAL_ROUND_WAIT_SECONDS` | `docs/ci/pr-automation.md` |
| `AE_CODEX_AUTOPILOT_ENABLED` | enable Codex Autopilot Lane | unset (off) | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_MAX_ROUNDS` | max autonomous rounds per PR | `3` | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_ROUND_WAIT_SECONDS` | wait between autopilot rounds | `8` | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_WAIT_STRATEGY` | wait strategy (`fixed` / `exponential`) | `fixed` | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_ROUND_WAIT_MAX_SECONDS` | max exponential wait | `AE_AUTOPILOT_ROUND_WAIT_SECONDS` | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_DRY_RUN` | dry-run mode without side effects | `false` | `docs/ci/codex-autopilot-lane.md` |

### 5. PR slash commands
Entry point: `.github/workflows/agent-commands.yml`

Operational note:
- Most PR commands are label-attachment commands and do not require trusted association.
- `/review` is the main exception and is restricted to trusted actors (`MEMBER` / `OWNER` / `COLLABORATOR`).
- Trace revalidation remains label-only through `run-trace` in the current repository.

#### 5.1 Main commands
- `/verify-lite`
  - runs `verify-lite.yml` through `workflow_dispatch`
- `/review [strict]`
  - dispatches verify-lite plus fast CI
  - `strict` adds coverage-oriented checks and `enforce-coverage`
- `/run-qa` / `/run-security` / `/run-cedar` / `/run-resilience` / `/run-spec` / `/run-drift` / `/run-hermetic` / `/run-formal`
  - attach the corresponding label and let workflow label conditions decide execution
- `/non-blocking` / `/blocking`
  - add or remove `ci-non-blocking`
- `/coverage <pct|clear>`
  - add or clear `coverage:<pct>`
- `/enforce-coverage`
  - force the coverage gate
- `/enforce-context-pack`
  - add `enforce-context-pack` to make Context Pack E2E blocking
- `/pr-digest` / `/pr-detailed`
  - switch PR summary output mode
- `/formal-help` / `/formal-quickstart`
  - post formal execution guidance into the PR

#### 5.2 Dispatch-oriented commands
These call workflow-dispatch entry points directly when the repository wants the manual-dispatch path.

- `/run-qa-dispatch`
- `/run-security-dispatch`
- `/ci-fast-dispatch`
- `/formal-verify-dispatch`
- `/formal-apalache-dispatch`
- `/run-flake-dispatch`
- `/spec-validation-dispatch`
- `/run-cedar-dispatch`
- `/formal-aggregate-dispatch`

### 6. Issue slash commands
Dual entrypoints exist:
- `.github/workflows/agent-commands.yml`
  - always enabled
  - no `author_association` restriction
- `.github/workflows/slash-commands.yml`
  - enabled only when `AE_SLASH_COMMANDS_ISSUE=1`
  - restricted to `MEMBER` / `OWNER` / `COLLABORATOR`

Representative commands:
- `/start` -> apply `status:in-progress` and assign the commenter
- `/plan` -> post the plan template comment
- `/ready-for-review` -> apply `status:review`
- `/block [reason]` -> apply `status:blocked`
- `/unblock` -> apply `status:in-progress`
- `/handoff <role:...>`
  - available only when `AE_SLASH_COMMANDS_ISSUE=1` enables `.github/workflows/slash-commands.yml`
  - attaches `role:*` labels and can assign according to `AE_ROLE_ASSIGNMENTS`
- `/handoff @user`
  - remains available through `.github/workflows/agent-commands.yml`
  - updates assignee and `status:review`

### 7. References
- `docs/ci/branch-protection-operations.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/copilot-auto-fix.md`
- `docs/ci/auto-merge.md`
- `docs/ci/pr-automation.md`
- `.github/workflows/verify-lite.yml`
- `.github/workflows/agent-commands.yml`
- `.github/workflows/slash-commands.yml`

---

## 日本語

## 1. 目的
PRやIssueで **必要な検証だけを opt-in で起動** し、CIコストとレビュー負荷を最小化するための操作カタログです。  
（一次情報: `.github/workflows/agent-commands.yml`, `.github/workflows/verify-lite.yml`, `.github/workflows/slash-commands.yml`）

## 2. 対象範囲
- PR向け: **ラベル** と **Slashコマンド（PRコメント）**
- Issue向け: **Slashコマンド（Issueコメント）**

## 3. PR向けラベル（代表）

| ラベル | 効果 | 起動/影響する主なWF・ジョブ | 補足 |
| --- | --- | --- | --- |
| `run-qa` | 次回の対象PRイベントで QA 相当のステップを有効化 | `ae-ci.yml` | `/run-qa` はラベル付与のみ。即時実行は `/run-qa-dispatch` を使う |
| `run-security` | 次回の対象PRイベントでセキュリティ/SBOM実行を有効化 | `security.yml`, `sbom-generation.yml`, `cedar-quality-gates.yml` | `/run-security` はラベル付与のみ。fork PR は引き続き制限あり |
| `run-cedar` | 次回の対象PRイベントで Cedar 品質ゲートを有効化 | `cedar-quality-gates.yml` | `/run-cedar` はラベル付与のみ。即時実行は `/run-cedar-dispatch` |
| `run-formal` | 次回の `verify-lite` 実行で形式検証を有効化 | `verify-lite.yml` 内 `Run formal` | verify-lite の label-gated。手動実行は `/formal-verify-dispatch` |
| `run-resilience` | 次回の `verify-lite` 実行で Resilience quick を有効化 | `verify-lite.yml` 内 `Resilience quick` | `/run-resilience` はラベル付与のみ |
| `run-hermetic` | 次回の対象PRイベントで Hermetic CI を有効化 | `ci.yml`, `hermetic-ci.yml` | `/run-hermetic` はラベル付与のみ。即時実行は dispatch 系を使う |
| `run-spec` | fail-fast spec validation の意図を記録 | `spec-validation.yml` | `/run-spec` は情報ラベルのみ。実行は `/spec-validation-dispatch` を使う |
| `run-trace` | KvOnce trace validation を required gate 対象として再評価 | `spec-generate-model.yml`（checks: `trace-conformance`, `KvOnce Trace Validation`） | 高リスクPRで `policy-gate` が参照（fork PRは `trace-conformance` で判定） |
| `run-drift` | codegen drift detection | `codegen-drift-check.yml` | `/run-drift` で付与 |
| `enforce-assurance` | assurance summary を strict 判定 | `verify-lite.yml` 内 `Enforce assurance summary (strict; label-gated)` | high-risk PR のみ推奨。運用手順は `docs/quality/assurance-operations-runbook.md` |
| `enforce-bdd-lint` | BDD lint を strict 化 | `verify-lite.yml` | `/enforce-bdd-lint` で付与 |
| `enforce-verify-lite-lint` | verify-lite lint baseline を enforce | `verify-lite.yml` | PRラベルで制御 |
| `enforce-context-pack` | Context Pack E2E を strict 化 | `context-pack-quality-gate.yml` | Phase C までの段階導入で利用 |
| `enforce-discovery` | Discovery Pack validate/compile を strict 化 | `verify-lite.yml` 内 Discovery Pack rollout | report-only 既定。strict では orphan / blocking open questions を fail 条件に昇格 |
| `ci-non-blocking` | 一部ジョブを non-blocking 化 | 各workflowのcontinue-on-error設定 | `/non-blocking` で付与 |
| `enforce-coverage` | coverageゲートの強制 | `coverage-check.yml` | `/enforce-coverage` で付与 |
| `coverage:<pct>` | coverage閾値上書き | `coverage-check.yml` | `/coverage 75` 等で付与 |
| `pr-summary:digest` | legacy 互換用の digest 意図を記録 | `pr-ci-status-comment.yml` | `/pr-digest` は互換ラベル追加のみ。現行は `pr-summary:detailed` が無ければ簡潔モード |
| `pr-summary:detailed` | 次回の PR Maintenance cycle で詳細モードを有効化 | `pr-ci-status-comment.yml` | `/pr-detailed` で付与。現行 renderer はこのラベルだけを参照 |
| `autopilot:on` | Codex Autopilot Lane 対象化 | `codex-autopilot-lane.yml` | touchless merge の opt-in |

補足: PR の自動化（auto-fix / auto-merge）は、ラベルではなく **Repository Variables** でプロジェクト単位に有効化できます。

| 変数 | 役割 | 既定 | 詳細 |
| --- | --- | --- | --- |
| `AE_AUTOMATION_PROFILE` | PR自動化の一括プロファイル（`conservative` / `balanced` / `aggressive`） | 未設定（無効） | `docs/ci/automation-profiles.md` |
| `AE_REVIEW_TOPOLOGY` | 承認トポロジ（`team` / `solo`） | `team` | `docs/ci/pr-automation.md`（topology対応版 policy-gate で有効） |
| `AE_POLICY_MIN_HUMAN_APPROVALS` | policy-gate の人手承認数を明示上書き（非負整数、空で無効） | 未設定 | `docs/ci/pr-automation.md`（topology対応版 policy-gate で有効） |
| `AE_POLICY_ENGINE_MODE` | policy shadow compare の実行モード（`shadow` / `shadow_strict`） | `shadow` | `docs/ci/pr-automation.md`（`shadow_strict` は mismatch を blocking） |
| `AE_COPILOT_AUTO_FIX` | Copilot suggestion 自動適用（ON/OFF） | 未設定（OFF） | `docs/ci/copilot-auto-fix.md` |
| `AE_COPILOT_AUTO_FIX_SCOPE` | 対象スコープ（`docs` / `all`） | `docs` | `docs/ci/copilot-auto-fix.md` |
| `AE_COPILOT_AUTO_FIX_LABEL` | ラベルopt-in（任意） | 未設定 | `docs/ci/copilot-auto-fix.md` |
| `AE_AUTO_MERGE` | auto-merge 自動有効化（ON/OFF） | 未設定（OFF） | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_MODE` | 対象方式（`all` / `label`） | `all` | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_LABEL` | opt-in ラベル名（`label` モード時） | 未設定 | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_REQUIRE_RISK_LOW` | `risk:low` ラベル必須化（`1`/`0`） | `1` | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE` | Change Package Validation 要約必須化（`1`/`0`） | `1` | `docs/ci/auto-merge.md` |
| `AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN` | Change Package Validation の `WARN` 許可（`1`/`0`） | `1` | `docs/ci/auto-merge.md` |

補足: 個別変数は `AE_AUTOMATION_PROFILE` より優先されます。

GitHub API の 429 / secondary rate limit が出る場合は、以下の Repository Variables で緩和できます（一次情報: `scripts/ci/lib/gh-exec.mjs`）。

| 変数 | 役割 | 既定 | 詳細 |
| --- | --- | --- | --- |
| `AE_GH_THROTTLE_MS` | `gh` 呼び出し間の最小間隔（ms） | `250`（`0`で無効化） | `docs/ci/pr-automation.md` |
| `AE_GH_RETRY_MAX_ATTEMPTS` | 最大試行回数（初回実行を含む） | `8` | `docs/ci/pr-automation.md` |
| `AE_GH_RETRY_INITIAL_DELAY_MS` | retry初期待ち（ms） | `750` | `docs/ci/pr-automation.md` |
| `AE_GH_RETRY_MAX_DELAY_MS` | retry最大待ち（ms） | `60000` | `docs/ci/pr-automation.md` |
| `AE_GH_RETRY_MULTIPLIER` | retry待機の指数倍率 | `2` | `docs/ci/pr-automation.md` |
| `AE_GH_RETRY_JITTER_MS` | retry待機に加えるランダムジッター上限（ms） | `250` | `docs/ci/pr-automation.md` |
| `AE_GH_RETRY_DEBUG` | retryログ出力（`1`） | 未設定 | `docs/ci/pr-automation.md` |

PR self-heal を使う場合は次も設定できます（一次情報: `.github/workflows/pr-self-heal.yml`, `scripts/ci/pr-self-heal.mjs`）。

| 変数 | 役割 | 既定 | 詳細 |
| --- | --- | --- | --- |
| `AE_SELF_HEAL_ENABLED` | self-heal workflow 有効化 | 未設定（OFF） | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_MAX_ROUNDS` | 1PRあたりの復旧ラウンド上限 | `3` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_MAX_AGE_MINUTES` | rerun対象にする失敗チェックの最大経過分 | `180` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_MAX_PRS` | schedule実行時に処理するPR数上限 | `20` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_ROUND_WAIT_SECONDS` | 復旧ラウンド間の待機秒 | `60` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_WAIT_STRATEGY` | 復旧ラウンド待機戦略（`fixed`/`exponential`） | `fixed` | `docs/ci/pr-automation.md` |
| `AE_SELF_HEAL_ROUND_WAIT_MAX_SECONDS` | 指数待機時の上限秒 | `AE_SELF_HEAL_ROUND_WAIT_SECONDS` | `docs/ci/pr-automation.md` |

Codex Autopilot Lane を使う場合:

| 変数 | 役割 | 既定 | 詳細 |
| --- | --- | --- | --- |
| `AE_CODEX_AUTOPILOT_ENABLED` | autopilot lane 有効化 | 未設定（OFF） | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_MAX_ROUNDS` | 1PRあたりの自律ループ上限 | `3` | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_ROUND_WAIT_SECONDS` | ループ間待機秒 | `8` | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_WAIT_STRATEGY` | ラウンド待機戦略（`fixed`/`exponential`） | `fixed` | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_ROUND_WAIT_MAX_SECONDS` | 指数待機時の上限秒 | `AE_AUTOPILOT_ROUND_WAIT_SECONDS` | `docs/ci/codex-autopilot-lane.md` |
| `AE_AUTOPILOT_DRY_RUN` | 副作用なし検証 | `false` | `docs/ci/codex-autopilot-lane.md` |
関連:
- PR自動化の全体像: `docs/ci/pr-automation.md`

## 4. PR向け Slash コマンド（PRコメント）

> 入口: `.github/workflows/agent-commands.yml`  
> 権限: 多くのコマンドは `author_association` 制限なし（ラベル付与型）。`/review` のみ trusted 必須（`MEMBER/OWNER/COLLABORATOR`）。

### 4.1 主要コマンド
- `/verify-lite`  
  - `verify-lite.yml` を workflow_dispatch で実行
- `/review [strict]`  
  - verify-lite + ci-fast を dispatch
  - `strict` なら coverage-check を追加 + `enforce-coverage` を付与
- `/run-qa` / `/run-security` / `/run-cedar` / `/run-resilience` / `/run-spec` / `/run-drift` / `/run-hermetic` / `/run-formal`  
  - 次回の対象PRイベントに向けて対応ラベルを付与
  - 既に open な PR で即時実行したい場合は `*-dispatch` を使う
- `/non-blocking` / `/blocking`  
  - `ci-non-blocking` の付与/解除
- `/coverage <pct|clear>`  
  - `coverage:<pct>` を付与／クリア
- `/enforce-coverage`  
  - coverage ゲートを強制
- `/enforce-context-pack`
  - `enforce-context-pack` を付与（Context Pack E2E を strict 化）
- `/pr-digest` / `/pr-detailed`  
  - `/pr-detailed` は次回の PR Maintenance cycle で詳細モードを有効化
  - `/pr-digest` は legacy 互換ラベルを付けるだけで、単独では `pr-summary:detailed` を上書きしない
- `/formal-help` / `/formal-quickstart`  
  - formal 実行のtipsをコメントで返す

### 4.2 dispatch 系コマンド（workflow_dispatch）
- `/run-qa-dispatch`
- `/run-security-dispatch`
- `/ci-fast-dispatch`
- `/formal-verify-dispatch`
- `/formal-apalache-dispatch`
- `/run-flake-dispatch`
- `/spec-validation-dispatch`
- `/run-cedar-dispatch`
- `/formal-aggregate-dispatch`

## 5. Issue向け Slash コマンド（Issueコメント）

> 入口（2系統）:  
> - `.github/workflows/agent-commands.yml`（常時有効 / `author_association` 制限なし）  
> - `.github/workflows/slash-commands.yml`（`AE_SLASH_COMMANDS_ISSUE=1` かつ `MEMBER/OWNER/COLLABORATOR` のみ）

- `/start` → `status:in-progress` 付与（commenter をアサイン）
- `/plan` → Planテンプレコメント
- `/ready-for-review` → `status:review`
- `/block [reason]` → `status:blocked`
- `/unblock` → `status:in-progress`
- `/handoff <role:...>` → `AE_SLASH_COMMANDS_ISSUE=1` で `.github/workflows/slash-commands.yml` が有効な場合のみ `role:*` ラベルを付与（`AE_ROLE_ASSIGNMENTS` によりアサイン）
- `/handoff @user` → 常時有効の `.github/workflows/agent-commands.yml` 側で assignee と `status:review` を設定

## 6. 参照ドキュメント
- Branch protection: `docs/ci/branch-protection-operations.md`
- Copilot Review Gate: `docs/ci/copilot-review-gate.md`
- Copilot Auto Fix: `docs/ci/copilot-auto-fix.md`
- Auto Merge: `docs/ci/auto-merge.md`
- Verify Lite: `.github/workflows/verify-lite.yml`
- Slash/Agent commands: `.github/workflows/agent-commands.yml`, `.github/workflows/slash-commands.yml`
