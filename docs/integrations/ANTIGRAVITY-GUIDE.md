# Antigravity Guide (draft)

## 目的
- Antigravity から ae-framework のテンプレを利用し、Spec→Test→Code→Verify を踏むための最小手順を示す。
- 入出力は Markdown/JSON に限定し、AJV/Schema で検証可能な形に固定する。

## 前提
- リポ構成: `spec/`, `tests/`, `plans/common/*` もしくは `plans/web-api/*`
- Antigravity 側で repo をチェックアウト済み、コマンド実行が可能

## 実行フロー（例）
1. 仕様生成
   - `plans/common/01-spec.md` をプロンプトとして渡し、OpenAPI/BDD/Property を生成
   - 生成先は必ずファイルパスで指定（例: `spec/api/openapi.yml`）
2. テスト骨子
   - `plans/common/02-tests.md` を渡し、テストスケルトンを生成（必要に応じて skip）
3. 実装
   - `plans/common/03-impl.md` を渡し、handler/service/repo を生成
4. 検証
   - `plans/common/04-verify.md` のコマンドをシェルで実行（lint/type/unit/integration/property）
5. PR 仕上げ
   - `plans/common/05-pr.md` をもとに PR 本文を作成

## 成果物検証
- Schema/JSON: `pnpm lint` / `pnpm spec:validate` が通ること
- テスト: `pnpm run test:fast`, `pnpm run test:property:webapi -- --runInBand --maxWorkers=50%`（対象に応じ調整）
- heavy-test (任意): `node scripts/pipelines/compare-test-trends.mjs ...`

## 注意
- 生成物は必ず Git 管理パスに出力させること
- 大きなファイルはアップロードせず、リンク/パス指定で指示
- 機密情報を含む入力を渡さない
