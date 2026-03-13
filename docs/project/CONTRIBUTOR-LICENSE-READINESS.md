---
docRole: ssot
canonicalSource: docs/project/CONTRIBUTOR-LICENSE-READINESS.md
lastVerified: "2026-03-13"
owner: project-docs
verificationCommand: pnpm run license:audit:contributors -- --scope-audit artifacts/reference/legal/license-scope-audit.json --output-json artifacts/reference/legal/contributor-license-readiness-audit.json --output-md artifacts/reference/legal/contributor-license-readiness-audit.md
---

# Contributor License Readiness

## 目的

`#2623` の Apache-2.0 切替判断に先立ち、repo 事実から観測できる contributor identity 情報を deterministic に固定する。

この監査は legal conclusion を出さない。以下だけを扱う。

- `license:audit:scope` が持つ contributor inventory の再整形
- human-like / bot-like / noreply identity の件数把握
- repo 事実だけでは relicensing authority を判断できないことの明示

## 実行コマンド

```bash
pnpm run license:audit:contributors -- \
  --scope-audit artifacts/reference/legal/license-scope-audit.json \
  --output-json artifacts/reference/legal/contributor-license-readiness-audit.json \
  --output-md artifacts/reference/legal/contributor-license-readiness-audit.md
```

`SOURCE_DATE_EPOCH=<unix-seconds>` を指定すると `generatedAt` を固定できる。

## 出力の見方

- `humanLikeCount`: bot-like / unknown を除く identity 件数
- `botLikeCount`: `bot`, `agent`, `Claude Code` などを含む identity 件数
- `noreplyCount`: `@users.noreply.github.com` を使う identity 件数
- `topContributorCommits`: repo 事実として観測される最大 commit 数

## 注意点

- 同一人物でも複数 identity で記録されている可能性がある
- repo 事実だけでは著作権者全員の合意や relicensing authority を判断できない
- この監査の用途は human/legal review に渡す factual input の固定である

## 関連資料

- `docs/project/LICENSE-MIGRATION-AUDIT.md`
- `docs/project/NOTICE-READINESS-AUDIT.md`
- `LICENSE-SCOPE.md`
