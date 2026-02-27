# Review Topology Matrix Validation

`policy-gate` の承認要件切替（`AE_REVIEW_TOPOLOGY` / `AE_POLICY_MIN_HUMAN_APPROVALS`）が
意図どおりに動作するかを、同一PRに対して比較検証する手順です。

## 1. 前提

- `GITHUB_TOKEN` が設定済みであること
- `GITHUB_REPOSITORY` が設定済みであること（例: `itdojp/ae-framework`）
- 検証対象の PR 番号が存在すること

## 2. 実行

```bash
GITHUB_TOKEN="$(gh auth token)" \
GITHUB_REPOSITORY=itdojp/ae-framework \
node scripts/ci/review-topology-matrix.mjs --pr 2314
```

生成物:
- `artifacts/ci/review-topology-matrix.json`
- `artifacts/ci/review-topology-matrix.md`

## 3. 検証シナリオ

- `team-default`
  - `AE_REVIEW_TOPOLOGY` 未設定
  - `AE_POLICY_MIN_HUMAN_APPROVALS` 未設定
- `solo`
  - `AE_REVIEW_TOPOLOGY=solo`
  - `AE_POLICY_MIN_HUMAN_APPROVALS` 未設定
- `team-override-2`
  - `AE_REVIEW_TOPOLOGY=team`
  - `AE_POLICY_MIN_HUMAN_APPROVALS=2`

## 4. 実行結果（2026-02-27, PR #2314）

| Scenario | Result | Approvals | Source | Error |
| --- | --- | --- | --- | --- |
| `team-default` | FAIL | `0/1` | `policy` | `human approvals are insufficient: required 1, got 0` |
| `solo` | PASS | `0/0` | `topology` | - |
| `team-override-2` | FAIL | `0/2` | `override` | `human approvals are insufficient: required 2, got 0` |

この結果により、同一PRで approvals 要件が `team -> solo -> override` の順に切替わることを確認できる。
