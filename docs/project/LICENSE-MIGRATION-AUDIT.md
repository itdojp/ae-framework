---
docRole: ssot
canonicalSource: docs/project/LICENSE-MIGRATION-AUDIT.md
lastVerified: "2026-03-13"
owner: project-docs
verificationCommand: pnpm run license:audit:all
---

# License Migration Audit

## 目的

`#2623` の Apache-2.0 移行前に、現行ライセンス状態と条件付きディレクトリの扱いを事実ベースで固定する。

## 現状

- root `LICENSE` は MIT
- root `package.json` の `license` field は `MIT`
- root には `LICENSE-SCOPE.md` / `TRADEMARKS.md` / `THIRD_PARTY_NOTICES.md` を追加済み
- root `NOTICE` は未作成
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

## 第一スライスの判断

- いきなり `LICENSE` を Apache-2.0 に差し替えない
- 先に監査結果で scope / conditional / nested notice を固定する
- contributor 観点の可否は repo 事実からは断定しない
- legal conclusion ではなく、実装側で扱える factual inventory を先に揃える

## 次段階

1. `artifacts/**`, `fixtures/**`, `test-cassettes/**` の由来を棚卸し
2. `NOTICE` の要否と草案を `pnpm run license:audit:all` の `notice` / `cutover` 出力で整理する
3. contributor identity を `pnpm run license:audit:all` の `contributors` 出力で factual input として固定する
4. third-party / upstream notice candidate を `pnpm run license:audit:all` の `third-party` 出力で factual input として固定する
5. `LICENSE-SCOPE.md` / `TRADEMARKS.md` / `THIRD_PARTY_NOTICES.md` を監査結果で具体化する
6. その後に Apache-2.0 切替可否を判断する

## 関連ドキュメント

- `docs/project/NOTICE-READINESS-AUDIT.md`
- `docs/project/CONTRIBUTOR-LICENSE-READINESS.md`
- `docs/project/THIRD-PARTY-NOTICE-CANDIDATES-AUDIT.md`
- `docs/project/APACHE-LICENSE-CUTOVER-PLAYBOOK.md`
- `docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md`
