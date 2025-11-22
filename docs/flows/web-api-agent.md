# Web API + DB フロー（エージェント併用）

## 入口
- Codex CLI: `plans/web-api/01-spec.md` 〜 `05-pr.md` を順番に実行
- 他エージェント（Antigravity/Gemini 等）でも、入出力を Markdown/JSON で維持する

## 実行のコツ
- 生成物はすべて Git 管理パスに書かせる（`spec/`, `tests/`, `src/web-api/`）
- OpenAPI/BDD/Property は必ずファイルパスを指定して上書きさせる
- AJV/スキーマで検証できる形式に限定し、YAML/JSON の lint を必須にする

## 実行手順（推奨）
1. 仕様生成
   - `plans/web-api/01-spec.md` を渡し、OpenAPI + BDD + Property の草案を生成
   - 生成後、AJV/Lint を実行（必要なら人手で整形）
2. テストスケルトン
   - `plans/web-api/02-tests.md` でテスト骨子を作成（必要に応じて `test.skip`）
3. 実装
   - `plans/web-api/03-impl.md` で handler/service/repo を実装
4. 検証
   - `plans/web-api/04-verify.md` のコマンドを順に実行
   - キャッシュ復元がある場合: `node scripts/pipelines/sync-test-results.mjs --restore`
   - トレンド比較: `node scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json`
5. PR 仕上げ
   - `plans/web-api/05-pr.md` のテンプレを PR 本文に貼り付け
   - 実行したテストとキャッシュ操作を明記

## 成果物検証
- OpenAPI: `pnpm ajv:lint`（スキーマバリデーションがある場合）
- Markdown: `pnpm lint:md`（存在すれば）
- テスト: `pnpm run test:fast`, `pnpm run test:integration -- --runInBand`, `pnpm run test:property -- --runInBand`
- Mutation（任意）: `STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick`

## Trace/ログのメモ先
- ExecPlan 実行ログは本ファイル末尾の `## Trace` セクションに追記（自由形式）

## Trace

（このセクションは実行ログのプレースホルダーです。必要に応じて追記してください）
