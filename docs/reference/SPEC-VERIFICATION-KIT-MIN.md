# Spec & Verification Kit (最小実用パッケージ) 草案

## 目的
- TypeScript を主軸に、仕様→テスト→検証を一括で有効化できる最小セットを定義する。
- もう1言語（例: Go）を追加できる拡張ポイントを明示する。

## 対象言語（初期）
- TypeScript (Node 20, pnpm)
- Go (オプション、fast-check 相当は `gopter` を候補)

## 含める要素（TS）
- BDD: `docs/templates/spec-kit/bdd-template.feature` + step スケルトンを `specs/bdd/` にコピーして利用 (CucumberJS)
- Property: `docs/templates/spec-kit/property-template.md` → `tests/property/**/*.test.ts` に写経可能なテンプレ + fast-check 設定
- Lint/Static/Type: `pnpm lint`, `pnpm types:check`, `pnpm run test:fast`
- CLI: `pnpm run test:property -- --runInBand`
- CI: `docs/templates/ci/spec-kit-min.workflow.yml` で lint/type/unit/property を一括実行（workflow_dispatch）

## 有効化フロー（TS）
1. `pnpm install` 後、下記を実行できる状態にする:
   - `pnpm lint`
   - `pnpm types:check`
   - `pnpm run test:fast`
   - `pnpm run test:property -- --runInBand`
2. `docs/templates/spec-kit/bdd-template.feature` と `docs/templates/spec-kit/property-template.md` をコピーして編集
3. `pnpm run test:property` が green になるようジェネレータ/不変条件を埋める
4. CI (workflow_dispatch テンプレ) で lint/type/unit/property を確認

## Go 追加時の拡張ポイント（メモ）
- テスト: `go test ./...`
- Property: `gopter` もしくは `rapid` を検討
- Lint: `golangci-lint run`
- Makefile/Taskfile で TS/Go の二言語をまとめて実行

## TODO（実装タスク）
- [x] `docs/templates/spec-kit/bdd-template.feature` と step スケルトンの追加（実行されない doc テンプレ）
- [x] `docs/templates/spec-kit/property-template.md` + fast-check boilerplate（ジェネレータ/不変条件入り）
- [x] `package.json` に `types:check`, `test:property` の標準スクリプトを確認・不足なら追加
- [x] CI テンプレ（workflow_dispatch）で lint/type/unit/property を並列 or 直列実行
- [ ] README/Docs に「有効化手順」を追記
