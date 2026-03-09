---
docRole: ssot
lastVerified: '2026-03-10'
owner: ui-e2e
verificationCommand: pnpm -s run check:doc-consistency
---
# UI Semantic E2E Lane

最小の UI semantic E2E lane です。スクリーンショット依存ではなく、role/name と ARIA tree を証跡として残します。

## Outputs

- `artifacts/e2e/ui-e2e-summary.json`
- `artifacts/e2e/ui-e2e-summary.md`
- `artifacts/e2e/summary.json`
- `artifacts/e2e/ui-aria-snapshots/*`

## Current minimal coverage

- `/ja/health`: operational status heading and service information
- `/ja/e2e/semantic-form`: accessible validation + submit flow

## Local run

```bash
pnpm run ui-e2e:semantic
```

既定では `@ae-framework/web` の Next dev server を `127.0.0.1:3100` で起動します。既存サーバを使う場合は次を使います。

```bash
pnpm run ui-e2e:semantic -- --base-url http://127.0.0.1:3000 --skip-server
```

## CI behavior

- workflow: `.github/workflows/parallel-test-execution.yml`
- lane: `test-e2e`
- trigger: PR では `run-e2e` ラベル時のみ、push では常時
- gate integration: `scripts/ci/build-harness-health.mjs` に optional gate `uiE2E` として統合

## Notes

- 失敗時は DOM snapshot ではなく、ARIA snapshot と role/name ベースの assertion message を残します。
- `artifacts/e2e/summary.json` は既存の adapter summary 集約へ流すための dual-write です。
- 現段階では `change-package` への evidence 必須化は行いません。これは次スライスで扱います。
