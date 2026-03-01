# CodeX Continuation Contract (No Human Bottleneck v1)

> Language / 言語: English | 日本語

---

## English (Summary)

This document defines the operational contract to keep CodeX execution moving without open-ended human handoffs.  
Each adapter response must be either:

1. **Continue**: `shouldBlockProgress=false` and executable `nextActions` are present.
2. **Blocked (justified)**: `shouldBlockProgress=true` and the minimum required human input is stated in one line.

Primary sources:
- `src/agents/task-types.ts`
- `schema/codex-task-response.schema.json`
- `scripts/codex/adapter-stdio.mjs`
- `scripts/ci/codex-autopilot-lane.mjs`

---

## 日本語

## 1. 目的

CodeX 実行で「確認待ち」「追加指示待ち」による停止を減らすため、`TaskResponse` の出力を継続実行可能な形に統一します。

適用範囲:
- ローカル実行（`pnpm run codex:adapter`）
- stdio ブリッジ（`scripts/codex/adapter-stdio.mjs`）
- CI の `Codex Autopilot Lane`

## 2. 継続実行 Contract（v1）

### 2.1 Continue（自走）

条件:
- `shouldBlockProgress=false`
- `nextActions.length >= 1`
- `nextActions` は実行可能な命令文（コマンド/操作）であること

禁止:
- 「どうしますか？」などのオープンエンド質問
- `nextActions=[]` のまま継続扱い

### 2.2 Blocked（正当停止）

条件:
- `shouldBlockProgress=true`
- `summary` または `warnings` に停止理由を明記
- 人間に必要な最小入力を1行で明記（曖昧な依頼を禁止）

v1 暫定表現（schema 拡張前）:
- `warnings` に `REQUIRED_INPUT: <key>=<value>` 形式を含める
- `nextActions` は `Provide <key>=<value> and rerun` のように1ステップで再開可能な記述にする

## 3. 推奨レスポンス例

### 3.1 Continue 例

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

### 3.2 Blocked 例

```json
{
  "summary": "Blocked: missing target environment",
  "analysis": "Release verify requires environment to evaluate policy overrides.",
  "recommendations": ["Set environment before rerun"],
  "nextActions": ["Provide environment=staging and rerun codex task"],
  "warnings": ["REQUIRED_INPUT: environment=staging|production"],
  "shouldBlockProgress": true
}
```

## 4. CI/Autopilot での停止理由と解除手順（deterministic）

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

## 5. ローカル検証レシピ

```bash
# 1) Build
pnpm run build

# 2) Adapter call
echo '{"description":"validate API","subagent_type":"validation","context":{}}' | pnpm run codex:adapter > /tmp/codex-response.json

# 3) Contract quick check (continue path)
jq -e '(.shouldBlockProgress == true) or ((.nextActions | length) > 0)' /tmp/codex-response.json

# 4) Schema validation path (adapter-stdio internally validates TaskResponse)
cat /tmp/codex-response.json | jq .
```

備考:
- 追加の相関制約（`shouldBlockProgress` と `nextActions` の厳密関係）は `#2338` で schema 側へ実装予定。

## 6. 一次情報

- 型定義: `src/agents/task-types.ts`
- レスポンススキーマ: `schema/codex-task-response.schema.json`
- stdio ブリッジ: `scripts/codex/adapter-stdio.mjs`
- CI 自動化: `scripts/ci/codex-autopilot-lane.mjs`
