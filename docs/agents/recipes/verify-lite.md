# Recipe: Verify Lite

## When to use

- PRの最小ゲートを局所再現したいとき

## Primary sources

- `docs/ci-policy.md`
- `.github/workflows/verify-lite.yml`

## Commands

```bash
pnpm -s run verify:lite
```

```bash
gh pr checks <PR_NUMBER> --required
```

## Expected output

- `verify-lite` が成功
- required checks の pending/fail 原因が特定できる

## Artifacts

- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/verify-lite/verify-lite-lint-summary.json`

## Follow-up

- fail時は PR に再現コマンド、失敗ステップ、修正方針を記録
