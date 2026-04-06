---
docRole: ssot
lastVerified: '2026-04-06'
owner: ui-e2e
verificationCommand: pnpm -s run check:doc-consistency
---
# UI Semantic E2E Lane

> Language / 言語: English | 日本語

---

## English

This is the minimum UI semantic E2E lane. It records role/name assertions and ARIA tree evidence instead of depending on screenshots.

### 出力

- `artifacts/e2e/ui-e2e-summary.json`
- `artifacts/e2e/ui-e2e-summary.md`
- `artifacts/e2e/summary.json`
- `artifacts/e2e/ui-aria-snapshots/*`

### Current minimal coverage

- `/ja/health`: operational status heading and service information
- `/ja/e2e/semantic-form`: accessible validation and submit flow

### ローカル実行

```bash
pnpm run ui-e2e:semantic
```

By default, this starts the `@ae-framework/web` Next dev server on `127.0.0.1:3100`. If an existing server is already running, use the following form.

```bash
pnpm run ui-e2e:semantic -- --base-url http://127.0.0.1:3000 --skip-server
```

### CI 挙動

- workflow: `.github/workflows/parallel-test-execution.yml`
- lane: `test-e2e`
- trigger: on PRs only when the `run-e2e` label is present; on push runs continuously
- ゲート統合（gate integration）: wired into `scripts/ci/build-harness-health.mjs` as the optional gate `uiE2E`

### 注記

- On failure, keep ARIA snapshots and role/name-based assertion messages rather than DOM snapshots.
- `artifacts/e2e/summary.json` remains a 二重書き込み（dual-write） path for the existing adapter summary aggregation.
- Evidence is not yet required in `change-package`; that belongs to a later rollout slice.

## 日本語

最小の UI semantic E2E lane です。スクリーンショット依存ではなく、role/name と ARIA tree を証跡として残します。

### 出力

- `artifacts/e2e/ui-e2e-summary.json`
- `artifacts/e2e/ui-e2e-summary.md`
- `artifacts/e2e/summary.json`
- `artifacts/e2e/ui-aria-snapshots/*`

### Current minimal coverage

- `/ja/health`: operational status heading and service information
- `/ja/e2e/semantic-form`: accessible validation + submit flow

### ローカル実行

```bash
pnpm run ui-e2e:semantic
```

既定では `@ae-framework/web` の Next dev server を `127.0.0.1:3100` で起動します。既存サーバを使う場合は次を使います。

```bash
pnpm run ui-e2e:semantic -- --base-url http://127.0.0.1:3000 --skip-server
```

### CI 挙動

- workflow: `.github/workflows/parallel-test-execution.yml`
- lane: `test-e2e`
- trigger: PR では `run-e2e` ラベル時のみ、push では常時
- ゲート統合（gate integration）: `scripts/ci/build-harness-health.mjs` に optional gate `uiE2E` として統合

### 注記

- 失敗時は DOM snapshot ではなく、ARIA snapshot と role/name ベースの assertion message を残します。
- `artifacts/e2e/summary.json` は既存の adapter summary 集約へ流すための 二重書き込み（dual-write） です。
- 現段階では `change-package` への evidence 必須化は行いません。これは次スライスで扱います。
