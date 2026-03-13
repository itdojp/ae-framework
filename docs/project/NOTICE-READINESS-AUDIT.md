---
docRole: ssot
canonicalSource: docs/project/NOTICE-READINESS-AUDIT.md
lastVerified: "2026-03-13"
owner: project-docs
verificationCommand: pnpm run license:audit:notice -- --scope-audit artifacts/reference/legal/license-scope-audit.json --conditional-audit artifacts/reference/legal/conditional-asset-audit.json --output-json artifacts/reference/legal/notice-readiness-audit.json --output-md artifacts/reference/legal/notice-readiness-audit.md
---

# Notice Readiness Audit

## 目的

`#2623` の Apache-2.0 切替可否判断に先立ち、root `NOTICE` を追加してよい状態かを事実ベースで整理する。

この監査は legal conclusion を出さない。目的は以下に限定する。

- 既存の factual audit をもとに root `NOTICE` の draft-only 文面を固定する
- nested notice と conditional assets の review が残っているかを明示する
- `LICENSE` 切替前に確認すべき cutover prerequisites を記録する

## 実行コマンド

```bash
pnpm run license:audit:notice -- \
  --scope-audit artifacts/reference/legal/license-scope-audit.json \
  --conditional-audit artifacts/reference/legal/conditional-asset-audit.json \
  --output-json artifacts/reference/legal/notice-readiness-audit.json \
  --output-md artifacts/reference/legal/notice-readiness-audit.md
```

`SOURCE_DATE_EPOCH=<unix-seconds>` を指定すると `generatedAt` を固定できる。

## 判定規則

- `nestedNoticeFiles` が 1 件でもあれば `needs-review`
- `runtime-output-or-unclassified` が 1 件でもあれば `needs-review`
- 上記 blocker が 0 件なら `draft-ready`

`draft-ready` は root `NOTICE` をすぐ有効化できることを意味しない。`LICENSE` 差し替え前の draft-only 準備完了を意味する。

## Proposed root NOTICE draft

監査結果には次の draft-only 文面を含める。

```text
ae-framework
Copyright (c) ae-framework contributors.
This product includes software developed by the ae-framework contributors.
```

この文面は root `NOTICE` の候補であり、`LICENSE` が Apache-2.0 へ切り替わるまで有効ではない。

## 関連資料

- `docs/project/LICENSE-MIGRATION-AUDIT.md`
- `LICENSE-SCOPE.md`
- `TRADEMARKS.md`
- `THIRD_PARTY_NOTICES.md`
