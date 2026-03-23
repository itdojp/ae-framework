---
docRole: derived
canonicalSource:
  - docs/agents/hook-feedback.md
  - docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-03-23'
---

# CodeX Continuation Contract (No Human Bottleneck v1)

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This document defines the continuation contract for CodeX task responses so execution does not stall on open-ended human handoffs. The output must always tell the operator or the automation lane whether work can continue immediately, and if not, what the minimum restart input is.

Applies to:
- local adapter execution (`pnpm run codex:adapter`)
- the stdio bridge (`scripts/codex/adapter-stdio.mjs`)
- CI automation through `scripts/ci/codex-autopilot-lane.mjs`

### 2. Continuation Contract (v1)

#### 2.1 Continue

Conditions:
- `shouldBlockProgress=false`
- `nextActions.length >= 1`
- every `nextActions[]` entry is directly executable as a command or deterministic operator action

Disallowed:
- open-ended questions such as "What should I do?"
- reporting success while leaving `nextActions=[]`

#### 2.2 Blocked (justified)

Conditions:
- `shouldBlockProgress=true`
- `warnings.length >= 1` with an explicit stop reason
- `nextActions.length >= 1` with a concrete restart step

Input-request representation:
- preferred: set both `blockingReason` and `requiredHumanInput`
- compatibility mode: include `REQUIRED_INPUT: <key>=<value>` in `warnings`
- in both modes, `nextActions` must stay restartable in one step, for example `Provide environment=staging and rerun codex task (PLAN)`; adapter normalization may append a phase suffix such as `(PLAN)` or `(EXEC)`
- keep `requiredHumanInput` to a one-line minimum, for example `approval=1` or `environment=staging|production`

### 3. Recommended response examples

#### 3.1 Continue example

```json
{
  "summary": "Generated formal artifacts for checkout flow",
  "analysis": "OpenAPI and TLA+ artifacts were written to artifacts/codex",
  "recommendations": ["Run verify gate on generated artifacts"],
  "nextActions": [
    "pnpm run verify:lite",
    "pnpm run verify:formal"
  ],
  "warnings": [],
  "shouldBlockProgress": false
}
```

#### 3.2 Blocked example

```json
{
  "summary": "Blocked: missing target environment",
  "analysis": "Release verify requires environment to evaluate policy overrides.",
  "recommendations": ["Set environment before rerun"],
  "nextActions": ["Provide environment=staging and rerun codex task"],
  "warnings": ["REQUIRED_INPUT: environment=staging|production"],
  "shouldBlockProgress": true,
  "blockingReason": "missing-environment",
  "requiredHumanInput": "environment=staging|production"
}
```

### 4. Deterministic stop reasons and unblocking paths in CI/autopilot

Representative stop reasons emitted by `scripts/ci/codex-autopilot-lane.mjs`:

| reason | Minimum unblock action |
| --- | --- |
| `missing label autopilot:on` | Add the `autopilot:on` label to the PR |
| `draft PR` | Mark the PR as ready for review |
| `merge conflict` | Merge `main`, resolve conflicts, and push |
| `checks healthy, waiting for required checks/merge queue` | Wait for required checks; no extra operator action |

Operational rules:
- add the `status:blocked` label only when `status=blocked`
- after unblocking, rerun autopilot through `/autopilot run` or `workflow_dispatch`

#### 4.1 Optional hook-feedback adapter

To rebuild a short continuation payload from existing CI artifacts:

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
```

- JSON output: `artifacts/agents/hook-feedback.json`
- Markdown output: `artifacts/agents/hook-feedback.md`
- continuation consumers should read `status`, `blockingReasons`, `nextActions`, and `reproCommands` first
- when `harness-health` or `change-package` is missing, the builder still succeeds and reflects the absence through `blockingReasons`, `nextActions`, `evidence.present=false`, and nullable `source.*Path`
- include `--context-pack-suggestions artifacts/context-pack/context-pack-suggestions.json` when that optional artifact exists
- add `--assurance-summary` or `--ui-e2e-summary` when those optional inputs are available and you need more specific continuation guidance

Variant with optional inputs:

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --ui-e2e-summary artifacts/e2e/ui-e2e-summary.json
```

#### 4.2 Adapter normalization rules (v1)

`src/agents/codex-task-adapter.ts` and `scripts/codex/adapter-stdio.mjs` normalize responses to reduce contract violations automatically.

| Condition | Normalization |
| --- | --- |
| `shouldBlockProgress=false` and `nextActions=[]` | Inject default phase-specific `nextActions` via `finalizeTaskResponse` |
| `shouldBlockProgress=true` and `summary` does not start with `Blocked:` | Prefix `Blocked:` |
| `shouldBlockProgress=true` and no restart action exists in `nextActions` | Inject `Provide ... and rerun codex task` at the top |
| `shouldBlockProgress=true` and `warnings=[]` inside the adapter | Inject `INTERNAL CONTRACT VIOLATION ...` |
| `requiredHumanInput` is missing but `warnings` contains `REQUIRED_INPUT:` | Infer and populate `requiredHumanInput` |
| `shouldBlockProgress=true` and `warnings=[]` in the stdio bridge | Inject `Human action: ...` using `requiredHumanInput`, `nextActions[0]`, `blockingReason`, or a generic fallback |

Notes:
- after normalization, the final response is validated by `schema/codex-task-response.schema.json`
- if normalization still cannot satisfy the contract, the stdio bridge fails closed with `INVALID_RESPONSE_SCHEMA` and exit code `1`

### 5. Local validation recipe

```bash
# 1) Build
pnpm run build

# 2) Adapter call
echo '{"description":"validate API","subagent_type":"validation","context":{}}' | pnpm run codex:adapter > /tmp/codex-response.json || test $? -eq 2

# 3) Contract quick checks
# continue response: nextActions must exist when shouldBlockProgress=false
jq -e 'if .shouldBlockProgress then true else ((.nextActions | length) > 0) end' /tmp/codex-response.json
# blocked response: nextActions and warnings must exist when shouldBlockProgress=true
jq -e 'if .shouldBlockProgress then ((.nextActions | length) > 0 and (.warnings | length) > 0) else true end' /tmp/codex-response.json

# 3.1) Representative unit tests
pnpm vitest run \
  tests/unit/agents/codex-task-adapter.test.ts \
  tests/unit/scripts/codex-adapter-stdio.test.ts \
  tests/unit/schema/codex-task-response-schema.test.ts

# 4) Optional standalone schema validation
node --input-type=module - <<'NODE'
import fs from 'node:fs';
import Ajv2020 from 'ajv/dist/2020.js';

const schema = JSON.parse(fs.readFileSync('schema/codex-task-response.schema.json', 'utf8'));
const data = JSON.parse(fs.readFileSync('/tmp/codex-response.json', 'utf8'));
const ajv = new Ajv2020({ allErrors: true, strict: false });
const validate = ajv.compile(schema);
if (!validate(data)) {
  console.error(JSON.stringify(validate.errors, null, 2));
  process.exit(1);
}
console.log('schema-valid');
NODE
```

Notes:
- `pnpm run codex:adapter` returns exit code `2` for blocked responses; this is expected
- use `pnpm run check:schemas` when you want to revalidate the schema cross-field constraints locally

### 6. Primary sources

- Type definitions: `src/agents/task-types.ts`
- Response schema: `schema/codex-task-response.schema.json`
- stdio bridge: `scripts/codex/adapter-stdio.mjs`
- CI automation: `scripts/ci/codex-autopilot-lane.mjs`

---

## 日本語

### 1. 目的

CodeX 実行で「確認待ち」「追加指示待ち」による停止を減らすため、`TaskResponse` の出力を継続実行可能な形に統一します。

適用範囲:
- ローカル実行（`pnpm run codex:adapter`）
- stdio ブリッジ（`scripts/codex/adapter-stdio.mjs`）
- CI の `Codex Autopilot Lane`

### 2. 継続実行 Contract（v1）

#### 2.1 Continue（自走）

条件:
- `shouldBlockProgress=false`
- `nextActions.length >= 1`
- `nextActions` は実行可能な命令文（コマンド/操作）であること

禁止:
- 「どうしますか？」などのオープンエンド質問
- `nextActions=[]` のまま継続扱い

#### 2.2 Blocked（正当停止）

条件:
- `shouldBlockProgress=true`
- `warnings.length >= 1`（停止理由を明記）
- `nextActions.length >= 1`（再開手順を明示）

入力要求の表現（互換運用）:
- 推奨: `blockingReason` と `requiredHumanInput` を明示する
- 互換: `warnings` に `REQUIRED_INPUT: <key>=<value>` を含める
- いずれの場合も `nextActions` は `Provide <key>=<value> and rerun codex task (PLAN)` のように1ステップで再開可能な記述にする。adapter の正規化で `(PLAN)` / `(EXEC)` のような phase suffix が付く場合があります
- `requiredHumanInput` は 1 行の最小入力（例: `approval=1` / `environment=staging|production`）に限定する

### 3. 推奨レスポンス例

#### 3.1 Continue 例

```json
{
  "summary": "Generated formal artifacts for checkout flow",
  "analysis": "OpenAPI and TLA+ artifacts were written to artifacts/codex",
  "recommendations": ["Run verify gate on generated artifacts"],
  "nextActions": [
    "pnpm run verify:lite",
    "pnpm run verify:formal"
  ],
  "warnings": [],
  "shouldBlockProgress": false
}
```

#### 3.2 Blocked 例

```json
{
  "summary": "Blocked: missing target environment",
  "analysis": "Release verify requires environment to evaluate policy overrides.",
  "recommendations": ["Set environment before rerun"],
  "nextActions": ["Provide environment=staging and rerun codex task"],
  "warnings": ["REQUIRED_INPUT: environment=staging|production"],
  "shouldBlockProgress": true,
  "blockingReason": "missing-environment",
  "requiredHumanInput": "environment=staging|production"
}
```

### 4. CI/Autopilot での停止理由と解除手順（deterministic）

`scripts/ci/codex-autopilot-lane.mjs` が出力する代表的な停止理由:

| reason | 解除手順（最小） |
| --- | --- |
| `missing label autopilot:on` | PR に `autopilot:on` ラベルを付与 |
| `draft PR` | Ready for review に変更 |
| `merge conflict` | `main` を取り込み、コンフリクト解消して push |
| `checks healthy, waiting for required checks/merge queue` | required checks 完了まで待機（追加操作不要） |

運用ルール:
- `status=blocked` のときのみ `status:blocked` ラベルを付与
- 解除後は autopilot を再実行（`/autopilot run` または workflow_dispatch）

#### 4.1 Optional hook feedback adapter

既存の CI artifact から continuation 用の短い feedback を再生成する場合は、次を実行します。

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
```

- 出力 JSON: `artifacts/agents/hook-feedback.json`
- 出力 Markdown: `artifacts/agents/hook-feedback.md`
- continuation 側は `status`, `blockingReasons`, `nextActions`, `reproCommands` を優先して読む
- `harness-health` / `change-package` が無い場合も builder は継続し、欠落は `blockingReasons` / `nextActions` / `evidence.present=false` / `source.*Path=null` に反映される
- `context-pack-suggestions` が存在する場合は `--context-pack-suggestions artifacts/context-pack/context-pack-suggestions.json` を追加する
- `assurance-summary` / `ui-e2e-summary` が存在する場合は optional input として追加し、continuation の `blockingReasons` / `nextActions` / `reproCommands` を具体化する

利用可能な optional input を含める場合は、次の variant を使います。

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --ui-e2e-summary artifacts/e2e/ui-e2e-summary.json
```

#### 4.2 Adapter 実装の正規化ルール（v1）

`src/agents/codex-task-adapter.ts` と `scripts/codex/adapter-stdio.mjs` は、Contract 違反を最小化するために次を自動補正します。

| 条件 | 正規化内容 |
| --- | --- |
| `shouldBlockProgress=false` かつ `nextActions=[]` | フェーズ別の既定 `nextActions` を補完（`finalizeTaskResponse`） |
| `shouldBlockProgress=true` かつ `summary` が `Blocked:` で始まらない | `Blocked:` 接頭辞を付与 |
| `shouldBlockProgress=true` かつ `nextActions` に再開アクションがない | `Provide ... and rerun codex task` を先頭へ注入 |
| `shouldBlockProgress=true` かつ `warnings=[]`（adapter内部） | `INTERNAL CONTRACT VIOLATION ...` を補完 |
| `requiredHumanInput` 未指定だが `warnings` に `REQUIRED_INPUT:` がある | `requiredHumanInput` を推論して設定 |
| `shouldBlockProgress=true` かつ `warnings=[]`（stdioブリッジ） | `Human action: ...` を補完（優先順: `requiredHumanInput` → `nextActions[0]` → `blockingReason` → 汎用文言） |

備考:
- これらの補正後に `schema/codex-task-response.schema.json` で最終検証されます。
- 補正不能な場合は stdio ブリッジが `INVALID_RESPONSE_SCHEMA`（exit `1`）で fail-closed します。

### 5. ローカル検証レシピ

```bash
# 1) Build
pnpm run build

# 2) Adapter call
echo '{"description":"validate API","subagent_type":"validation","context":{}}' | pnpm run codex:adapter > /tmp/codex-response.json || test $? -eq 2

# 3) Contract quick checks
# continue response: shouldBlockProgress=false なら nextActions は1件以上
jq -e 'if .shouldBlockProgress then true else ((.nextActions | length) > 0) end' /tmp/codex-response.json
# blocked response: shouldBlockProgress=true なら nextActions/warnings は各1件以上
jq -e 'if .shouldBlockProgress then ((.nextActions | length) > 0 and (.warnings | length) > 0) else true end' /tmp/codex-response.json

# 3.1) 代表ユニットテスト（Contract/Adapter/Schema）
pnpm vitest run \
  tests/unit/agents/codex-task-adapter.test.ts \
  tests/unit/scripts/codex-adapter-stdio.test.ts \
  tests/unit/schema/codex-task-response-schema.test.ts

# 4) Optional: standalone schema validation
node --input-type=module - <<'NODE'
import fs from 'node:fs';
import Ajv2020 from 'ajv/dist/2020.js';

const schema = JSON.parse(fs.readFileSync('schema/codex-task-response.schema.json', 'utf8'));
const data = JSON.parse(fs.readFileSync('/tmp/codex-response.json', 'utf8'));
const ajv = new Ajv2020({ allErrors: true, strict: false });
const validate = ajv.compile(schema);
if (!validate(data)) {
  console.error(JSON.stringify(validate.errors, null, 2));
  process.exit(1);
}
console.log('schema-valid');
NODE
```

備考:
- `pnpm run codex:adapter` は blocked 応答時に exit code `2` を返します（想定動作）。
- schema の相関制約をローカルで再確認する場合は `pnpm run check:schemas` を実行します。

### 6. 一次情報

- 型定義: `src/agents/task-types.ts`
- レスポンススキーマ: `schema/codex-task-response.schema.json`
- stdio ブリッジ: `scripts/codex/adapter-stdio.mjs`
- CI 自動化: `scripts/ci/codex-autopilot-lane.mjs`
