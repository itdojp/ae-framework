---
name: Web API feature (Agentic SDLC)
about: Spec/Test-first issue for Web API + DB flow
labels: roadmap
---

## Summary
- 概要:
- ユースケース/ビジネス価値:

## Scope
- エンドポイント:
- DB テーブル/モデル:
- 依存サービス:

## Spec links
- OpenAPI: spec/api/openapi.yml (対象セクションを明記)
- BDD: spec/bdd/web-api-sample.md (対象シナリオを列挙)
- Property: spec/properties/web-api-sample.md (対象プロパティを列挙)

## Acceptance criteria (例)
- [ ] BDD シナリオが実装され、integration テストが green
- [ ] Property テストの主要 invariant が実装され green
- [ ] エラー時に監査ログ/イベントが発火

## Tests to run
- [ ] pnpm run lint
- [ ] pnpm run test:fast
- [ ] pnpm run test:integration -- --runInBand
- [ ] pnpm run test:property -- --runInBand --maxWorkers=50%
- [ ] STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick (任意)

## Notes
- キャッシュ活用: sync-test-results.mjs (restore/store/snapshot)
- トレンド比較: compare-test-trends.mjs → reports/heavy-test-trends.json
