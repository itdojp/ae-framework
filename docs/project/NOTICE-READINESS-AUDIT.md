---
docRole: ssot
canonicalSource: docs/project/NOTICE-READINESS-AUDIT.md
lastVerified: "2026-03-14"
owner: project-docs
verificationCommand: pnpm run license:audit:notice -- --scope-audit artifacts/reference/legal/license-scope-audit.json --conditional-audit artifacts/reference/legal/conditional-asset-audit.json --output-json artifacts/reference/legal/notice-readiness-audit.json --output-md artifacts/reference/legal/notice-readiness-audit.md
---

# Notice Readiness Audit

## 目的

`#2623` / `#2673` の actual cutover で root `NOTICE` を追加する根拠になった事実ベース監査を記録する。

この監査は legal conclusion を出さない。目的は以下に限定する。

- 既存の factual audit をもとに root `NOTICE` の承認済み文面を固定する
- nested notice と conditional assets の review が残っているかを明示する
- ただし、`docs/` / `tests/` / `schema/` / `fixtures/` / `artifacts/` / `test-cassettes/` 配下の first-party audit/test 文書は nested notice blocker から除外する
- `LICENSE` 切替前に確認すべき cutover prerequisites を記録する

## 実行コマンド

```bash
pnpm run license:audit:notice -- \
  --scope-audit artifacts/reference/legal/license-scope-audit.json \
  --conditional-audit artifacts/reference/legal/conditional-asset-audit.json \
  --output-json artifacts/reference/legal/notice-readiness-audit.json \
  --output-md artifacts/reference/legal/notice-readiness-audit.md
```

`SOURCE_DATE_EPOCH=<unix-seconds>` を指定すると `generatedAt` を固定できる。出力 JSON / Markdown には `gitHeadSha` も含まれ、scope / conditional audit と同一 head かを比較できる。

## 判定規則

- review relevant な `nestedNoticeFiles` が 1 件でもあれば `needs-review`
- `runtime-output-or-unclassified` が 1 件でもあれば `needs-review`
- 上記 blocker が 0 件なら `draft-ready`

`draft-ready` は root `NOTICE` を即時有効化できることを意味しない。pre-cutover head で actual cutover に進める準備が整ったことを意味する。

監査結果には `ignoredNestedNoticeFilesCount` も含まれ、first-party audit/test 文書由来の notice-like filename が何件除外されたかを追跡できる。

## Approved root NOTICE text

監査結果には次の承認済み文面を含める。

```text
ae-framework
Copyright (c) ae-framework contributors.
This product includes software developed by the ae-framework contributors.
```

この文面は root `NOTICE` の承認済みテキストであり、actual cutover changeset で採用した。

## 関連資料

- `docs/project/LICENSE-MIGRATION-AUDIT.md`
- `LICENSE-SCOPE.md`
- `TRADEMARKS.md`
- `THIRD_PARTY_NOTICES.md`
