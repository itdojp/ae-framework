---
docRole: ssot
canonicalSource: docs/project/LICENSE-MIGRATION-AUDIT.md
lastVerified: "2026-03-13"
owner: project-docs
verificationCommand: pnpm run license:audit:scope -- --output-json artifacts/reference/legal/license-scope-audit.json --output-md artifacts/reference/legal/license-scope-audit.md
---

# License Migration Audit

## 目的

`#2623` の Apache-2.0 移行前に、現行ライセンス状態と条件付きディレクトリの扱いを事実ベースで固定する。

## 現状

- root `LICENSE` は MIT
- root `package.json` に `license` field は未設定
- root には `NOTICE` / `LICENSE-SCOPE.md` / `TRADEMARKS.md` / `THIRD_PARTY_NOTICES.md` は未作成
- `artifacts/**`, `fixtures/**`, `test-cassettes/**` は first-party 固定ではなく、由来確認が必要な条件付きディレクトリとして扱う

## 監査コマンド

```bash
pnpm run license:audit:scope -- \
  --output-json artifacts/reference/legal/license-scope-audit.json \
  --output-md artifacts/reference/legal/license-scope-audit.md
```

## 監査観点

1. tracked file を以下に分類する
   - first-party
   - first-party root files
   - conditional (`artifacts/**`, `fixtures/**`, `test-cassettes/**`)
   - other
2. tracked な nested `LICENSE*` / `NOTICE*` / `COPYING*` を列挙する
3. `git shortlog -sne --all` から contributor inventory を生成する
4. root `LICENSE` と `package.json` の現行値を記録する

## 第一スライスの判断

- いきなり `LICENSE` を Apache-2.0 に差し替えない
- 先に監査結果で scope / conditional / nested notice を固定する
- contributor 観点の可否は repo 事実からは断定しない
- legal conclusion ではなく、実装側で扱える factual inventory を先に揃える

## 次段階

1. `LICENSE-SCOPE.md` のドラフト化
2. `TRADEMARKS.md` と `THIRD_PARTY_NOTICES.md` の骨子作成
3. `artifacts/**`, `fixtures/**`, `test-cassettes/**` の由来を棚卸し
4. その後に Apache-2.0 切替可否を判断する
