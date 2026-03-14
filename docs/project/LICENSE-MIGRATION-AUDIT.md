---
docRole: ssot
canonicalSource: docs/project/LICENSE-MIGRATION-AUDIT.md
lastVerified: "2026-03-14"
owner: project-docs
verificationCommand: pnpm run license:audit:all
---

# License Migration Audit

## 目的

`#2623` / `#2673` の Apache-2.0 cutover を支えた pre-cutover factual audit を記録する。

## 現状

- root `LICENSE` は Apache-2.0
- root `package.json` の `license` field は `Apache-2.0`
- root `NOTICE` は追加済み
- root には `LICENSE-SCOPE.md` / `TRADEMARKS.md` / `THIRD_PARTY_NOTICES.md` を配置済み
- `artifacts/**`, `fixtures/**`, `test-cassettes/**` は first-party 固定ではなく、由来確認が必要な条件付きディレクトリとして扱う

## 監査コマンド

```bash
SOURCE_DATE_EPOCH=<unix-seconds> pnpm run license:audit:all
```

`license:audit:all` は以下の 6 audit を `artifacts/reference/legal/*` へ順番に再生成する。

- `license:audit:scope`
- `license:audit:conditional`
- `license:audit:notice`
- `license:audit:contributors`
- `license:audit:third-party`
- `license:audit:cutover`

`SOURCE_DATE_EPOCH=<unix-seconds>` を指定すると、全 audit の `generatedAt` を固定して再現可能な snapshot を得る。各 legal audit artifact は `gitHeadSha` も出力するため、同一 head で生成した監査結果だけを比較対象にできる。

completed approval record が揃った後の最終 preflight は以下を使う。

```bash
SOURCE_DATE_EPOCH=<unix-seconds> pnpm run license:audit:precutover -- \
  --approval-record docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md
```

`license:audit:precutover` は `license:audit:all` を再実行した後、同じ output directory 上で `license:audit:approval` を実行する。

## 監査観点

1. tracked file を以下に分類する
   - first-party
   - first-party root files
   - conditional (`artifacts/**`, `fixtures/**`, `test-cassettes/**`)
   - other
2. root legal files を除いた tracked な nested `LICENSE*` / `NOTICE*` / `COPYING*` を列挙する
3. `git shortlog -sne --all` から contributor inventory を生成する
4. root `LICENSE` と `package.json` の現行値を記録する
5. tracked nested legal file / vendored path / submodule の有無を deterministic に列挙する
6. 以降の notice / contributor / cutover readiness 監査では、入力 audit の `gitHeadSha` が一致していることを前提条件にする

## Pre-cutover audit notes

- `license:audit:all` と `license:audit:precutover` は pre-cutover head での factual evidence を固定するための監査である
- actual cutover 後の branch head では `apache-license-cutover-readiness-audit/v1` が MIT baseline 前提のため blocked になる
- そのため cutover PR では、直前の pre-cutover head で取得した audit evidence を approval record と合わせて参照する

## 記録した実施順序

1. `artifacts/**`, `fixtures/**`, `test-cassettes/**` の由来を棚卸し
2. `NOTICE` の要否と草案を `pnpm run license:audit:all` の `notice` / `cutover` 出力で整理する
3. contributor identity を `pnpm run license:audit:all` の `contributors` 出力で factual input として固定する
4. third-party / upstream notice candidate を `pnpm run license:audit:all` の `third-party` 出力で factual input として固定する
5. cutover approval record の completeness を `pnpm run license:audit:approval` で機械検証し、最終 preflight は `pnpm run license:audit:precutover` で再現可能にする
6. `LICENSE-SCOPE.md` / `TRADEMARKS.md` / `THIRD_PARTY_NOTICES.md` を監査結果で具体化する
7. human/legal approval 完了後に actual cutover を実行する

## 関連ドキュメント

- `docs/project/NOTICE-READINESS-AUDIT.md`
- `docs/project/CONTRIBUTOR-LICENSE-READINESS.md`
- `docs/project/THIRD-PARTY-NOTICE-CANDIDATES-AUDIT.md`
- `docs/project/APACHE-LICENSE-CUTOVER-PLAYBOOK.md`
- `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md`
- `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-READINESS.md`
