---
docRole: derived
canonicalSource:
- docs/ci-policy.md
- .github/workflows/verify-lite.yml
- docs/ci/ci-troubleshooting-guide.md
lastVerified: '2026-03-31'
---

# Recipe: Verify Lite

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you need to reproduce the minimum required PR gate locally
- when you need to identify why required checks remain `pending` or `fail`
- when you need a focused first pass before escalating to broader CI investigation

### What to load (primary sources)
- `docs/ci-policy.md`
- `.github/workflows/verify-lite.yml`
- `docs/ci/ci-troubleshooting-guide.md`

### Commands (copy/paste)
Start with the local baseline, then compare the result with the GitHub required-check view.

```bash no-doctest
pnpm -s run verify:lite
```

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

```bash no-doctest
gh pr view <PR_NUMBER> --json mergeable,mergeStateStatus,url
```

### Expected output
- local `verify-lite` completes without failures
- the failing or pending required check is narrowed down before you touch broader workflows
- the next escalation step is supported by a concrete artifact path or required-check URL

### Artifacts to check
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/verify-lite/verify-lite-lint-summary.json`
- the latest `verify-lite` job summary and required-check URLs from `gh pr checks <PR_NUMBER> --required`

### First fields to inspect
- in `artifacts/verify-lite/verify-lite-run-summary.json`, inspect the top-level `steps` object first and isolate the entries whose status is not successful
- if `traceability` exists, inspect `traceability.status`, `traceability.missingCount`, and `traceability.matrixPath` before re-running traceability-specific validation
- if the local run is green but the PR check is still failing, compare the required-check URL with the branch freshness and the latest head SHA before changing code

### Follow-up
- when `verify-lite` fails locally, record the reproduction command, the first failing step, and the artifact path directly in the PR
- when local `verify-lite` passes but GitHub still fails, treat branch freshness, stale runs, and unresolved review threads as the next likely causes
- escalate to `docs/ci/ci-troubleshooting-guide.md` when the failure scope expands beyond the minimum gate

## 日本語

### When to use
- PR の最小 required gate をローカルで再現したいとき
- required checks が `pending` / `fail` のまま残る原因を切り分けたいとき
- より広い CI 調査へ進む前に、最小単位の確認を行いたいとき

### What to load (primary sources)
- `docs/ci-policy.md`
- `.github/workflows/verify-lite.yml`
- `docs/ci/ci-troubleshooting-guide.md`

### Commands (copy/paste)
まずローカル baseline を実行し、その結果を GitHub の required checks 表示と照合します。

```bash no-doctest
pnpm -s run verify:lite
```

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

```bash no-doctest
gh pr view <PR_NUMBER> --json mergeable,mergeStateStatus,url
```

### Expected output
- ローカルの `verify-lite` が失敗なく完了する
- failing / pending の required check を、より広い workflow に触る前に絞り込める
- 次の escalation が、具体的な artifact path または required-check URL に基づいて説明できる

### Artifacts to check
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/verify-lite/verify-lite-lint-summary.json`
- `gh pr checks <PR_NUMBER> --required` で確認できる最新 `verify-lite` job summary と required-check URL

### First fields to inspect
- `artifacts/verify-lite/verify-lite-run-summary.json` では、まず top-level の `steps` を確認し、successful でない項目を切り分ける
- `traceability` が存在する場合は、traceability 固有の再検証に進む前に `traceability.status`、`traceability.missingCount`、`traceability.matrixPath` を確認する
- ローカルが green なのに PR check が fail の場合は、コード変更に進む前に required-check URL、branch freshness、最新 head SHA を照合する

### Follow-up
- ローカル `verify-lite` が fail した場合は、再現コマンド、最初の failing step、artifact path をそのまま PR に記録する
- ローカルが pass でも GitHub が fail の場合は、次の原因候補として branch freshness、stale run、未解消 review thread を優先して確認する
- 最小 gate を越える調査が必要になったら `docs/ci/ci-troubleshooting-guide.md` へ escalation する
