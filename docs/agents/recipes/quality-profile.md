# Recipe: Quality Profile

## When to use

- PRで重い検証をどこまで起動するかを判断したいとき

## Primary sources

- `docs/ci-policy.md`
- `docs/ci/OPT-IN-CONTROLS.md`
- `policy/risk-policy.yml`

## Commands

```bash
gh pr view <PR_NUMBER> --json labels,files
```

```bash
gh pr comment <PR_NUMBER> --body '/review strict'
```

```bash
gh pr comment <PR_NUMBER> --body '/run-security'
```

## Expected output

- 変更内容に対応するラベルとdispatchが適切に選択される

## Artifacts

- PRラベル履歴
- `policy-gate` サマリ
- Security/coverage系ジョブログ

## Follow-up

- 不要な heavy job は解除し、必要な gate は理由付きで維持する
