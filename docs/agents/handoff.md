# AE-HANDOFF Protocol

エージェント間ハンドオフ時の最小プロトコルです。  
Change Package（#2289）の詳細要約を代替するものではなく、存在する場合は参照します。

## Purpose

- 次担当エージェントが「何を確認し、何を実行し、どの証跡を見るか」を即決できる状態にする
- PR/Issueコメントの粒度を標準化し、属人化を抑制する

## Required fields

1. Goal
2. Current status
3. Next actions（順序付き）
4. Commands run
5. Artifacts
6. Risks / Rollback note（必要時）
7. Blockers（詰まりがある場合）

## Optional field

- Change Package reference  
  - 例: `artifacts/change-package/summary.md`
  - Change Packageが未整備の場合は `n/a` と明記

## Usage

- PR上で `/handoff A|B|C` を実行し、ハンドオフ先ラベルを付与
- その後、`templates/comments/AE-HANDOFF.md` をベースにコメントを投稿
- `Next actions` は1ステップずつ実行可能な粒度にする

## Example (minimal)

```md
## AE-HANDOFF
- Goal: policy-gateのfail原因を解消し、required checksをgreen化する
- Current status: risk-label mismatchは解消済み。review gateがpending。
- Next actions:
  1. gate jobログ確認
  2. 必要ならworkflow_dispatchで再評価
- Commands run: `gh pr checks 1234 --required`
- Artifacts: `artifacts/ci/policy-gate-summary.json`
- Risks / Rollback note: workflow変更時はrevert PRで即時復旧可能
- Blockers: human approval 1件待ち
- Change Package: n/a
```
