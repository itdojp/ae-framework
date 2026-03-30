---
docRole: ssot
lastVerified: '2026-03-31'
owner: agent-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# AE-HANDOFF Protocol

> 🌍 Language / 言語: English | 日本語

---

## English

### Overview
This document defines the minimum handoff protocol between agents. It does not replace the detailed summary in a Change Package. When a Change Package exists, reference it from the handoff instead of duplicating that detail.

### Purpose
- let the next agent decide immediately what to inspect, what to run, and which evidence to read
- standardize PR and issue handoff comments so the handoff process does not depend on individual writing style

### Standard outputs
- JSON sidecar: `artifacts/handoff/ae-handoff.json`
- Markdown sidecar: `artifacts/handoff/ae-handoff.md`
- Schema: `schema/ae-handoff.schema.json`
- Builder: `pnpm run handoff:create -- --goal "<goal>"`
- Validator: `pnpm run handoff:validate -- artifacts/handoff/ae-handoff.json schema/ae-handoff.schema.json`

### Required fields
1. Goal
2. Current status
3. Next actions in execution order
4. Commands run
5. Artifacts
6. Risks / rollback note when needed
7. Blockers when present

### Optional fields
- Change Package reference
  - example: `artifacts/change-package/summary.md`
  - if no Change Package exists, record `n/a`

### JSON sidecar mapping
| Markdown field | JSON field |
| --- | --- |
| Goal | `goal` |
| Current status | `currentStatus` |
| Next actions | `nextActions[]` |
| Commands run | `commandsRun[]` |
| Artifacts | `artifacts[]` |
| Risks / rollback note | `risksRollbackNote` |
| Blockers | `blockers[]` |
| Change Package | `changePackageRef` |

### Usage
- when generating deterministic sidecars, start with `pnpm run handoff:create -- --goal "<goal>" --target "A"`
- if `artifacts/agents/hook-feedback.json` is absent, the builder derives content from `artifacts/verify-lite/verify-lite-run-summary.json` and companion artifacts
- if `artifacts/assurance/assurance-summary.json` exists, pass `--assurance-summary` so assurance warnings are reflected into `currentStatus`, `nextActions`, `blockers`, and `artifacts`
- `commandsRun` prefers explicitly provided commands; otherwise it falls back to repro commands from hook feedback
- if JSON sidecars were generated, validate them with `pnpm run handoff:validate -- artifacts/handoff/ae-handoff.json schema/ae-handoff.schema.json`

### Current repository note
- PR comments use `/handoff A|B|C` for agent-target handoff
- issue comments can use `/handoff @user` through `agent-commands.yml` to assign and move toward review
- keep that distinction explicit when documenting operating flows

### Builder examples
```bash
pnpm run handoff:create -- \
  --goal "prepare this branch for human review" \
  --target "A" \
  --command-run "pnpm -s run verify:lite"
```

```bash
pnpm run handoff:create -- \
  --goal "handoff current CI investigation" \
  --hook-feedback artifacts/agents/missing-hook-feedback.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json \
  --policy-gate-summary artifacts/ci/policy-gate-summary.json
```

### Minimal Markdown example
```md
## AE-HANDOFF
- Goal: resolve the policy-gate failure and return required checks to green
- Current status: risk-label mismatch is fixed; gate is still pending
- Next actions:
  1. inspect the gate job log
  2. re-run policy evaluation if needed
- Commands run: `gh pr checks 1234 --required`
- Artifacts: `artifacts/ci/policy-gate-summary.json`
- Risks / Rollback note: a workflow change can be reverted immediately with a revert PR
- Blockers: waiting for one human approval
- Change Package: n/a
```

### JSON example
```json
{
  "schemaVersion": "ae-handoff/v1",
  "generatedAt": "2026-03-09T09:00:00.000Z",
  "handoffTarget": "A",
  "goal": "resolve the policy-gate failure and return required checks to green",
  "currentStatus": "risk-label mismatch is fixed; gate is still pending.",
  "nextActions": [
    {
      "order": 1,
      "summary": "inspect the gate job log",
      "command": "gh pr checks 1234 --required"
    },
    {
      "order": 2,
      "summary": "re-run policy evaluation if needed",
      "command": "gh workflow run policy-gate.yml"
    }
  ],
  "commandsRun": [
    "gh pr checks 1234 --required"
  ],
  "artifacts": [
    {
      "path": "artifacts/ci/policy-gate-summary.json",
      "description": "latest policy-gate summary"
    }
  ],
  "risksRollbackNote": "a workflow change can be reverted immediately with a revert PR",
  "blockers": [
    {
      "summary": "waiting for one human approval",
      "kind": "human"
    }
  ],
  "changePackageRef": null
}
```

## 日本語

### 概要
本ドキュメントは、エージェント間ハンドオフの最小プロトコルを定義します。Change Package の詳細要約を置き換えるものではありません。Change Package が存在する場合は、その内容を重複記述するのではなく参照してください。

### Purpose
- 次担当エージェントが、何を確認し、何を実行し、どの証跡を確認するかを即決できる状態にする
- PR / issue の handoff comment を標準化し、属人化を抑制する

### Standard outputs
- JSON sidecar: `artifacts/handoff/ae-handoff.json`
- Markdown sidecar: `artifacts/handoff/ae-handoff.md`
- Schema: `schema/ae-handoff.schema.json`
- Builder: `pnpm run handoff:create -- --goal "<goal>"`
- Validator: `pnpm run handoff:validate -- artifacts/handoff/ae-handoff.json schema/ae-handoff.schema.json`

### Required fields
1. Goal
2. Current status
3. 実行順付きの Next actions
4. Commands run
5. Artifacts
6. 必要時の Risks / rollback note
7. 該当する場合の Blockers

### Optional fields
- Change Package reference
  - 例: `artifacts/change-package/summary.md`
  - Change Package がなければ `n/a` を記録する

### JSON sidecar mapping
| Markdown field | JSON field |
| --- | --- |
| Goal | `goal` |
| Current status | `currentStatus` |
| Next actions | `nextActions[]` |
| Commands run | `commandsRun[]` |
| Artifacts | `artifacts[]` |
| Risks / rollback note | `risksRollbackNote` |
| Blockers | `blockers[]` |
| Change Package | `changePackageRef` |

### Usage
- deterministic sidecar を生成する場合は、まず `pnpm run handoff:create -- --goal "<goal>" --target "A"` から開始する
- `artifacts/agents/hook-feedback.json` がない場合、builder は `artifacts/verify-lite/verify-lite-run-summary.json` と companion artifacts から内容を導出する
- `artifacts/assurance/assurance-summary.json` がある場合は `--assurance-summary` を指定し、assurance warning を `currentStatus`、`nextActions`、`blockers`、`artifacts` に反映する
- `commandsRun` は明示指定を優先し、未指定時は hook feedback の repro command を fallback とする
- JSON sidecar を生成した場合は、`pnpm run handoff:validate -- artifacts/handoff/ae-handoff.json schema/ae-handoff.schema.json` で検証する

### 現行 repository 注記
- PR comment では agent-target handoff として `/handoff A|B|C` を使う
- issue comment では `agent-commands.yml` 経由で `/handoff @user` を使い、assign と review 方向への遷移を行える
- 運用フローを記述する際は、この区別を明示する

### Builder examples
```bash
pnpm run handoff:create -- \
  --goal "prepare this branch for human review" \
  --target "A" \
  --command-run "pnpm -s run verify:lite"
```

```bash
pnpm run handoff:create -- \
  --goal "handoff current CI investigation" \
  --hook-feedback artifacts/agents/missing-hook-feedback.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json \
  --policy-gate-summary artifacts/ci/policy-gate-summary.json
```

### Minimal Markdown example
```md
## AE-HANDOFF
- Goal: policy-gate の fail 原因を解消し、required checks を green に戻す
- Current status: risk-label mismatch は解消済み。gate はまだ pending。
- Next actions:
  1. gate job log を確認する
  2. 必要なら policy evaluation を再実行する
- Commands run: `gh pr checks 1234 --required`
- Artifacts: `artifacts/ci/policy-gate-summary.json`
- Risks / Rollback note: workflow 変更は revert PR で即時復旧できる
- Blockers: human approval 1 件待ち
- Change Package: n/a
```

### JSON example
```json
{
  "schemaVersion": "ae-handoff/v1",
  "generatedAt": "2026-03-09T09:00:00.000Z",
  "handoffTarget": "A",
  "goal": "policy-gate の fail 原因を解消し、required checks を green に戻す",
  "currentStatus": "risk-label mismatch は解消済み。gate はまだ pending。",
  "nextActions": [
    {
      "order": 1,
      "summary": "gate job log を確認する",
      "command": "gh pr checks 1234 --required"
    },
    {
      "order": 2,
      "summary": "必要なら policy evaluation を再実行する",
      "command": "gh workflow run policy-gate.yml"
    }
  ],
  "commandsRun": [
    "gh pr checks 1234 --required"
  ],
  "artifacts": [
    {
      "path": "artifacts/ci/policy-gate-summary.json",
      "description": "latest policy-gate summary"
    }
  ],
  "risksRollbackNote": "workflow 変更は revert PR で即時復旧できる",
  "blockers": [
    {
      "summary": "human approval 1 件待ち",
      "kind": "human"
    }
  ],
  "changePackageRef": null
}
```
