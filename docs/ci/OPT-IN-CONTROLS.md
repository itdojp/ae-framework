# Opt-in Controls Catalog（ラベル / Slash / dispatch）

> Language / 言語: English | 日本語

---

## English (Summary)

This document catalogs PR labels and slash commands that opt-in heavy CI jobs or change gating behavior. It is derived from `.github/workflows/agent-commands.yml`, `verify-lite.yml`, and related workflows.

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
| `run-qa` | QA相当のステップ実行 | `ae-ci.yml` | `/run-qa` で付与 |
| `run-security` | セキュリティ/SBOM実行 | `security.yml`, `sbom-generation.yml`, `cedar-quality-gates.yml` | fork PRは制限あり |
| `run-cedar` | Cedar品質ゲート実行（report-only想定） | `cedar-quality-gates.yml` | `/run-cedar` で付与 |
| `run-formal` | 形式検証実行 | `verify-lite.yml` 内 `Run formal` | verify-lite の label-gated |
| `run-resilience` | Resilience quick実行 | `verify-lite.yml` 内 `Resilience quick` | `/run-resilience` で付与 |
| `run-hermetic` | Hermetic CI 実行 | `ci.yml`, `hermetic-ci.yml` | `/run-hermetic` で付与 |
| `run-spec` | fail-fast spec validation | `spec-validation.yml` | `/run-spec` で付与 |
| `run-drift` | codegen drift detection | `codegen-drift-check.yml` | `/run-drift` で付与 |
| `enforce-bdd-lint` | BDD lint を strict 化 | `verify-lite.yml` | `/enforce-bdd-lint` で付与 |
| `enforce-verify-lite-lint` | verify-lite lint baseline を enforce | `verify-lite.yml` | PRラベルで制御 |
| `enforce-context-pack` | Context Pack E2E を strict 化 | `context-pack-quality-gate.yml` | Phase C までの段階導入で利用 |
| `ci-non-blocking` | 一部ジョブを non-blocking 化 | 各workflowのcontinue-on-error設定 | `/non-blocking` で付与 |
| `enforce-coverage` | coverageゲートの強制 | `coverage-check.yml` | `/enforce-coverage` で付与 |
| `coverage:<pct>` | coverage閾値上書き | `coverage-check.yml` | `/coverage 75` 等で付与 |
| `pr-summary:digest` | PR summary を簡潔化 | `pr-ci-status-comment.yml` | `/pr-digest` で付与 |
| `pr-summary:detailed` | PR summary を詳細化 | `pr-ci-status-comment.yml` | `/pr-detailed` で付与 |
| `autopilot:on` | Codex Autopilot Lane 対象化 | `codex-autopilot-lane.yml` | touchless merge の opt-in |

補足: PR の自動化（auto-fix / auto-merge）は、ラベルではなく **Repository Variables** でプロジェクト単位に有効化できます。

| 変数 | 役割 | 既定 | 詳細 |
| --- | --- | --- | --- |
| `AE_AUTOMATION_PROFILE` | PR自動化の一括プロファイル（`conservative` / `balanced` / `aggressive`） | 未設定（無効） | `docs/ci/automation-profiles.md` |
| `AE_REVIEW_TOPOLOGY` | 承認トポロジ（`team` / `solo`） | `team` | `docs/ci/pr-automation.md` |
| `AE_POLICY_MIN_HUMAN_APPROVALS` | policy-gate の人手承認数を明示上書き（非負整数、空で無効） | 未設定 | `docs/ci/pr-automation.md` |
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
  - 対応ラベルを付与し、ラベル条件で各WFを起動
- `/non-blocking` / `/blocking`  
  - `ci-non-blocking` の付与/解除
- `/coverage <pct|clear>`  
  - `coverage:<pct>` を付与／クリア
- `/enforce-coverage`  
  - coverage ゲートを強制
- `/enforce-context-pack`
  - `enforce-context-pack` を付与（Context Pack E2E を strict 化）
- `/pr-digest` / `/pr-detailed`  
  - PR summary の出力モードを切替
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
- `/handoff <role:...>` → `role:*` ラベルを付与（`AE_ROLE_ASSIGNMENTS` によりアサイン）

## 6. 参照ドキュメント
- Branch protection: `docs/ci/branch-protection-operations.md`
- Copilot Review Gate: `docs/ci/copilot-review-gate.md`
- Copilot Auto Fix: `docs/ci/copilot-auto-fix.md`
- Auto Merge: `docs/ci/auto-merge.md`
- Verify Lite: `.github/workflows/verify-lite.yml`
- Slash/Agent commands: `.github/workflows/agent-commands.yml`, `.github/workflows/slash-commands.yml`
