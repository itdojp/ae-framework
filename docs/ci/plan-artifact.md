---
docRole: ssot
lastVerified: '2026-03-11'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Plan Artifact

`plan-artifact/v1` は high-risk PR の**事前レビュー契約**です。

- plan artifact: before-change review
- change package: after-change evidence

## 出力

- `artifacts/plan/plan-artifact.json`
- `artifacts/plan/plan-artifact.md`
- `artifacts/plan/plan-artifact-validation.json`
- `artifacts/plan/plan-artifact-validation.md`

## 生成

```bash
pnpm run plan-artifact:generate -- \
  --input artifacts/plan/plan-artifact.input.json \
  --output-json artifacts/plan/plan-artifact.json \
  --output-md artifacts/plan/plan-artifact.md
```

## 検証

```bash
pnpm run plan-artifact:validate -- \
  --file artifacts/plan/plan-artifact.json \
  --schema schema/plan-artifact.schema.json
```

## 最小 high-risk PR フロー

1. PR を作成し、`risk:high` を確定する。
2. `artifacts/plan/plan-artifact.json` / `.md` を commit する。
3. 人手レビュアは diff より先に plan artifact を確認する。
4. 実装後は `change-package` を生成し、before/after の責務を分離する。

## 運用メモ

- `policy-gate` は high-risk PR で plan artifact の存在と schema validation を確認する。
- `policy/risk-policy.yml` の `high_risk.require_plan_artifact=true` が既定であり、high-risk PR では plan artifact 不在を block する。
- low-risk PR では plan artifact は任意です。
- `pr-ci-status-comment.yml` は commit 済み `artifacts/plan/plan-artifact.json` がある場合、validation 結果を PR summary に追記します。
