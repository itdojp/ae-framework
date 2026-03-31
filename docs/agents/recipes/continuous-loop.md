---
docRole: derived
canonicalSource:
- docs/integrations/CODEX-CONTINUATION-CONTRACT.md
- schema/codex-task-response.schema.json
- docs/ci-policy.md
- policy/risk-policy.yml
- docs/ci/codex-autopilot-lane.md
lastVerified: '2026-03-31'
---

# Recipe: Continuous Loop Contract (CodeX)

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you want to reduce how often CodeX stops with a generic "waiting for next instruction" response
- when you need to verify that `TaskResponse` satisfies Continuation Contract v1
- when you need deterministic handling for blocked reasons and unblock steps in the `autopilot:on` lane

### Primary sources
- `docs/integrations/CODEX-CONTINUATION-CONTRACT.md`
- `schema/codex-task-response.schema.json`
- `docs/ci-policy.md`
- `policy/risk-policy.yml`
- `docs/ci/codex-autopilot-lane.md`

### Contract rules (v1)
- when `shouldBlockProgress=false`, provide at least one `nextActions` entry
- when `shouldBlockProgress=true`, provide an explicit stop reason or required input in `warnings[0]` and at least one `nextActions` entry with unblock steps
- for blocked responses, `warnings` must state why progress is blocked or what input is required; concrete restart steps or minimum human actions belong in `nextActions`
- do not use open-ended questions such as "What do you want to do?"
- when choices are needed, restrict them to 2-4 options and mark one option as recommended

### Commands
```bash no-doctest
pnpm -s run verify:lite
```

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

```bash no-doctest
echo '{"description":"validate API","subagent_type":"validation","context":{}}' | pnpm run codex:adapter
```

### TaskResponse examples
#### Unblocked (continue)
```json no-doctest
{
  "summary": "Validation completed without blockers",
  "analysis": "Schema and traceability checks passed for the current scope.",
  "recommendations": [
    "Run required checks before merge"
  ],
  "nextActions": [
    "pnpm -s run verify:lite",
    "gh pr checks 1234 --required"
  ],
  "warnings": [],
  "shouldBlockProgress": false
}
```

#### Blocked (justified)
```json no-doctest
{
  "summary": "Blocked: missing policy labels for autopilot lane",
  "analysis": "Risk policy requires labels before auto-merge lane can continue.",
  "recommendations": [
    "Add required labels and rerun autopilot lane"
  ],
  "nextActions": [
    "gh pr edit 1234 --add-label enforce-testing --add-label run-security"
  ],
  "warnings": [
    "REQUIRED_INPUT: required-labels=enforce-testing,run-security"
  ],
  "shouldBlockProgress": true,
  "blockingReason": "missing-policy-labels",
  "requiredHumanInput": "required-labels=enforce-testing,run-security"
}
```

### Follow-up
- for blocked responses, rewrite `nextActions[0]` into a directly executable command or operator step
- for `autopilot:on` PRs, prioritize the unblock procedure in `docs/ci/codex-autopilot-lane.md`
- for high-risk changes, satisfy the required labels/checks in `policy/risk-policy.yml` before retrying the lane

## 日本語

### When to use
- CodeX 運用で「次の指示待ち」で止まる頻度を減らしたいとき
- `TaskResponse` が継続実行 Contract v1 を満たしているか確認したいとき
- `autopilot:on` レーンで blocked 理由と解除手順を deterministic に扱いたいとき

### Primary sources
- `docs/integrations/CODEX-CONTINUATION-CONTRACT.md`
- `schema/codex-task-response.schema.json`
- `docs/ci-policy.md`
- `policy/risk-policy.yml`
- `docs/ci/codex-autopilot-lane.md`

### Contract rules (v1)
- `shouldBlockProgress=false` のときは `nextActions` を 1 件以上にする
- `shouldBlockProgress=true` のときは、停止理由または必要入力を `warnings[0]` に明示し、解除手順を含む `nextActions` を 1 件以上用意する
- blocked 応答では、`warnings` に停止理由や必要入力を書き、具体的な再開手順や人間の最小 1 手は `nextActions` に置く
- 「どうしますか？」のような open-ended question は使わない
- 選択肢が必要な場合は 2〜4 個に制限し、推奨案を 1 つ明示する

### Commands
```bash no-doctest
pnpm -s run verify:lite
```

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

```bash no-doctest
echo '{"description":"validate API","subagent_type":"validation","context":{}}' | pnpm run codex:adapter
```

### TaskResponse examples
#### Unblocked (continue)
```json no-doctest
{
  "summary": "Validation completed without blockers",
  "analysis": "Schema and traceability checks passed for the current scope.",
  "recommendations": [
    "Run required checks before merge"
  ],
  "nextActions": [
    "pnpm -s run verify:lite",
    "gh pr checks 1234 --required"
  ],
  "warnings": [],
  "shouldBlockProgress": false
}
```

#### Blocked (justified)
```json no-doctest
{
  "summary": "Blocked: missing policy labels for autopilot lane",
  "analysis": "Risk policy requires labels before auto-merge lane can continue.",
  "recommendations": [
    "Add required labels and rerun autopilot lane"
  ],
  "nextActions": [
    "gh pr edit 1234 --add-label enforce-testing --add-label run-security"
  ],
  "warnings": [
    "REQUIRED_INPUT: required-labels=enforce-testing,run-security"
  ],
  "shouldBlockProgress": true,
  "blockingReason": "missing-policy-labels",
  "requiredHumanInput": "required-labels=enforce-testing,run-security"
}
```

### Follow-up
- blocked 応答時は `nextActions[0]` を、そのまま実行できる command または operator step に書き換える
- `autopilot:on` PR では `docs/ci/codex-autopilot-lane.md` の blocked 解除手順を優先する
- 高リスク変更では、`policy/risk-policy.yml` の required labels / checks を先に満たしてから再試行する
