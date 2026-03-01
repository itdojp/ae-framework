# Recipe: Continuous Loop Contract (CodeX)

## When to use

- CodeX 運用で「次の指示待ち」で止まる頻度を減らしたいとき
- `TaskResponse` が継続実行 Contract v1 を満たしているか確認したいとき
- `autopilot:on` レーンで blocked 理由と解除手順を deterministic に扱いたいとき

## Primary sources

- `docs/integrations/CODEX-CONTINUATION-CONTRACT.md`
- `schema/codex-task-response.schema.json`
- `docs/ci-policy.md`
- `policy/risk-policy.yml`
- `docs/ci/codex-autopilot-lane.md`

## Contract rules (v1)

- `shouldBlockProgress=false` のときは `nextActions` を 1 件以上にする
- `shouldBlockProgress=true` のときは停止理由と人間の最小 1 手を明示する
- オープンエンド質問（例:「どうしますか？」）は使わない
- 選択肢が必要な場合は 2〜4 個に制限し、推奨案を 1 つ明示する

## Commands

```bash
pnpm -s run verify:lite
```

```bash
gh pr checks <PR_NUMBER> --required
```

```bash
echo '{"description":"validate API","subagent_type":"validation","context":{}}' | pnpm run codex:adapter
```

## TaskResponse examples

### Unblocked (continue)

```json
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

### Blocked (justified)

```json
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
    "Add labels: enforce-testing, run-security"
  ],
  "shouldBlockProgress": true,
  "blockingReason": "missing-policy-labels",
  "requiredHumanInput": "required-labels=enforce-testing,run-security"
}
```

## Follow-up

- blocked 応答時は `nextActions[0]` をそのまま実行できる形に修正する
- `autopilot:on` PR は `docs/ci/codex-autopilot-lane.md` の blocked 解除手順を優先する
- 高リスク変更は `policy/risk-policy.yml` の required labels/checks を先に満たしてから再試行する
