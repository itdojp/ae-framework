---
docRole: ssot
lastVerified: '2026-03-25'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Review Topology Matrix Validation

This document defines how to compare approval-requirement switching in `policy-gate` using the same PR. / 本ドキュメントは、`policy-gate` の承認要件切替を同一 PR 上で比較検証する手順を定義します。

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

Use this procedure to verify that `policy-gate` switches approval requirements correctly when `AE_REVIEW_TOPOLOGY` and `AE_POLICY_MIN_HUMAN_APPROVALS` change.

### 2. Prerequisites

- `GITHUB_TOKEN` or `GH_TOKEN` is configured
- `GITHUB_REPOSITORY` is configured, for example `itdojp/ae-framework`
- the target PR number exists

### 3. Run

```bash
GITHUB_TOKEN="$(gh auth token)" \
GITHUB_REPOSITORY=itdojp/ae-framework \
node scripts/ci/review-topology-matrix.mjs --pr 2314
```

Outputs:
- `artifacts/ci/review-topology-matrix.json`
- `artifacts/ci/review-topology-matrix.md`

### 4. Validation scenarios

- `team-default`
  - `AE_REVIEW_TOPOLOGY` unset
  - `AE_POLICY_MIN_HUMAN_APPROVALS` unset
- `solo`
  - `AE_REVIEW_TOPOLOGY=solo`
  - `AE_POLICY_MIN_HUMAN_APPROVALS` unset
- `team-override-2`
  - `AE_REVIEW_TOPOLOGY=team`
  - `AE_POLICY_MIN_HUMAN_APPROVALS=2`

### 5. Representative result (2026-02-27, PR #2314)

| Scenario | Result | Approvals | Source | Error |
| --- | --- | --- | --- | --- |
| `team-default` | FAIL | `0/1` | `policy` | `human approvals are insufficient: required 1, got 0` |
| `solo` | PASS | `0/0` | `topology` | - |
| `team-override-2` | FAIL | `0/2` | `override` | `human approvals are insufficient: required 2, got 0` |

This result shows that the same PR changes approval requirements in the order `team -> solo -> override`.

## 日本語

`policy-gate` の承認要件切替（`AE_REVIEW_TOPOLOGY` / `AE_POLICY_MIN_HUMAN_APPROVALS`）が
意図どおりに動作するかを、同一PRに対して比較検証する手順です。

## 1. 前提

- `GITHUB_TOKEN` または `GH_TOKEN` が設定済みであること
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
