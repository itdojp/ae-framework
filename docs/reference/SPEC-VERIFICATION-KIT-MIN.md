---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Spec & Verification Kit (最小実用パッケージ) 草案

## English

### Purpose
- Define the minimum package that enables specification, tests, and verification together with TypeScript as the primary language.
- Make the extension points explicit so a second language such as Go can be added later without redesigning the baseline kit.

### Initial language targets
- TypeScript (`Node 20`, `pnpm`)
- Go (optional; `gopter` is the current candidate for a fast-check equivalent)

### Included elements (TypeScript)
- BDD: copy `docs/templates/spec-kit/bdd-template.feature` and the step skeleton into `spec/bdd/` for CucumberJS-based examples.
- Property testing: use `docs/templates/spec-kit/property-template.md` as the seed for authored tests under `tests/property/**/*.test.ts`; the current minimum `pnpm run test:property` path still validates the built-in property harness smoke check unless you wire custom suites separately.
- Lint / static / type checks: `pnpm lint`, `pnpm types:check`, `pnpm run test:fast`
- CLI entrypoint: `pnpm run test:property`
- CI template: `docs/templates/ci/spec-kit-min.workflow.yml` runs lint, type, unit, and the minimum property harness check via `workflow_dispatch`
- Template seed: `templates/spec-kit-min/` provides a minimum repo bootstrap layout; runnable BDD files still need to live under `spec/bdd/**`

### Activation flow (TypeScript)
1. After `pnpm install`, make sure the following commands are runnable:
   - `pnpm lint`
   - `pnpm types:check`
   - `pnpm run test:fast`
   - `pnpm run test:property`
2. Copy and edit `docs/templates/spec-kit/bdd-template.feature` and `docs/templates/spec-kit/property-template.md`
3. Fill in generators and invariants for your authored property tests, while keeping the minimum property harness green with `pnpm run test:property`
4. Confirm lint, type, unit, and the minimum property harness check through the `workflow_dispatch` CI template

### Extension points when adding Go
- Tests: `go test ./...`
- Property testing: evaluate `gopter` or `rapid`
- Lint: `golangci-lint run`
- Coordinate TypeScript and Go execution through a shared `Makefile` or `Taskfile`

### TODO (implementation status)
- [x] Add `docs/templates/spec-kit/bdd-template.feature` and the step skeleton as documentation-first templates
- [x] Add `docs/templates/spec-kit/property-template.md` with fast-check boilerplate, generators, and invariants
- [x] Confirm `types:check` and `test:property` in `package.json`, and add them if missing
- [x] Provide a `workflow_dispatch` CI template for lint, type, unit, and property checks
- [x] Add `templates/spec-kit-min/` as the minimum initialization seed/template repository layout
- [x] Add activation guidance to README / docs

## 日本語

### 目的
- TypeScript を主軸に、仕様→テスト→検証を一括で有効化できる最小セットを定義する。
- もう1言語（例: Go）を追加できる拡張ポイントを明示する。

### 対象言語（初期）
- TypeScript (Node 20, pnpm)
- Go (オプション、fast-check 相当は `gopter` を候補)

### 含める要素（TS）
- BDD: `docs/templates/spec-kit/bdd-template.feature` + step スケルトンを `spec/bdd/` にコピーして利用 (CucumberJS)
- Property: `docs/templates/spec-kit/property-template.md` は `tests/property/**/*.test.ts` 向けの設計テンプレ。現行の最小 `pnpm run test:property` 経路は、custom suite を自動で読まず、組み込みの property harness smoke check を検証する
- Lint/Static/Type: `pnpm lint`, `pnpm types:check`, `pnpm run test:fast`
- CLI: `pnpm run test:property`
- CI: `docs/templates/ci/spec-kit-min.workflow.yml` で lint/type/unit/最小 property harness を一括実行（workflow_dispatch）
- Template seed: `templates/spec-kit-min/` は repo 初期化用の最小雛形。実行対象になる BDD ファイルは `spec/bdd/**` 配下へ置く

### 有効化フロー（TS）
1. `pnpm install` 後、下記を実行できる状態にする:
   - `pnpm lint`
   - `pnpm types:check`
   - `pnpm run test:fast`
   - `pnpm run test:property`
2. `docs/templates/spec-kit/bdd-template.feature` と `docs/templates/spec-kit/property-template.md` をコピーして編集
3. authored property tests 用のジェネレータ/不変条件を整えつつ、最小 property harness の `pnpm run test:property` を green に保つ
4. CI (workflow_dispatch テンプレ) で lint/type/unit/最小 property harness を確認

### Go 追加時の拡張ポイント（メモ）
- テスト: `go test ./...`
- Property: `gopter` もしくは `rapid` を検討
- Lint: `golangci-lint run`
- Makefile/Taskfile で TS/Go の二言語をまとめて実行

### TODO（実装タスク）
- [x] `docs/templates/spec-kit/bdd-template.feature` と step スケルトンの追加（実行されない doc テンプレ）
- [x] `docs/templates/spec-kit/property-template.md` + fast-check boilerplate（ジェネレータ/不変条件入り）
- [x] `package.json` に `types:check`, `test:property` の標準スクリプトを確認・不足なら追加
- [x] CI テンプレ（workflow_dispatch）で lint/type/unit/property を並列 or 直列実行
- [x] など初期化テンプレ/テンプレ repo で一式生成（`templates/spec-kit-min/` を追加）
- [x] README/Docs に「有効化手順」を追記
