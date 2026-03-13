---
docRole: ssot
canonicalSource: docs/project/APACHE-LICENSE-CUTOVER-READINESS.md
lastVerified: "2026-03-13"
owner: project-docs
verificationCommand: pnpm run license:audit:cutover -- --scope-audit artifacts/reference/legal/license-scope-audit.json --conditional-audit artifacts/reference/legal/conditional-asset-audit.json --notice-readiness-audit artifacts/reference/legal/notice-readiness-audit.json --contributor-readiness-audit artifacts/reference/legal/contributor-license-readiness-audit.json --output-json artifacts/reference/legal/apache-license-cutover-readiness-audit.json --output-md artifacts/reference/legal/apache-license-cutover-readiness-audit.md
---

# Apache License Cutover Readiness

## 目的

`#2623` の Apache-2.0 cutover 前に、既存の factual audit を 1 つの readiness summary に集約する。

この監査は legal conclusion を出さない。目的は以下に限定する。

- `LICENSE` 差し替え前に残っている blocker を固定する
- human/legal review が必要な理由を明示する
- cutover PR に入れるべき前提条件を deterministic に再生成できるようにする

## 実行コマンド

```bash
pnpm run license:audit:cutover -- \
  --scope-audit artifacts/reference/legal/license-scope-audit.json \
  --conditional-audit artifacts/reference/legal/conditional-asset-audit.json \
  --notice-readiness-audit artifacts/reference/legal/notice-readiness-audit.json \
  --contributor-readiness-audit artifacts/reference/legal/contributor-license-readiness-audit.json \
  --output-json artifacts/reference/legal/apache-license-cutover-readiness-audit.json \
  --output-md artifacts/reference/legal/apache-license-cutover-readiness-audit.md
```

`SOURCE_DATE_EPOCH=<unix-seconds>` を指定すると `generatedAt` を固定できる。

## 判定規則

- `blocked`
  - MIT baseline が欠落
  - notice readiness が `draft-ready` ではない
  - nested notice review または unclassified conditional asset が残る
- `human-review-required`
  - factual blocker は解消済みだが、relicensing authority の判断が人手レビューに残る
- `ready`
  - blocker がなく、かつ human/legal review requirement も消えている場合のみ

現時点の設計では、通常は `human-review-required` を返す。`ready` は将来、明示的な authority 確認フローが追加された場合のために予約している。

## 関連資料

- `docs/project/LICENSE-MIGRATION-AUDIT.md`
- `docs/project/NOTICE-READINESS-AUDIT.md`
- `docs/project/CONDITIONAL-ASSET-PROVENANCE-AUDIT.md`
- `docs/project/CONTRIBUTOR-LICENSE-READINESS.md`
