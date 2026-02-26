# Agent Commands Catalog

> この文書は `.github/workflows/agent-commands.yml` から自動生成されます。手動編集しないでください。

## PR向け Slash Commands

- `/blocking`
- `/ci-fast-dispatch`
- `/coverage`
- `/enforce-a11y`
- `/enforce-bdd-lint`
- `/enforce-context-pack`
- `/enforce-contracts`
- `/enforce-coverage`
- `/enforce-formal`
- `/enforce-lh`
- `/enforce-perf`
- `/enforce-typecov`
- `/formal-aggregate-dispatch`
- `/formal-apalache-dispatch`
- `/formal-help`
- `/formal-quickstart`
- `/formal-verify-dispatch`
- `/handoff`
- `/lh`
- `/non-blocking`
- `/perf`
- `/pr-detailed`
- `/pr-digest`
- `/qa-batch-agents`
- `/qa-batch-cli`
- `/qa-batch-commands`
- `/qa-batch-property`
- `/ready`
- `/review`
- `/run-adapters`
- `/run-cedar`
- `/run-cedar-dispatch`
- `/run-drift`
- `/run-flake-dispatch`
- `/run-formal`
- `/run-hermetic`
- `/run-qa`
- `/run-qa-dispatch`
- `/run-qa:agents`
- `/run-qa:cli`
- `/run-qa:commands`
- `/run-qa:property`
- `/run-resilience`
- `/run-security`
- `/run-security-dispatch`
- `/run-spec`
- `/spec-validation-dispatch`
- `/verify-lite`

## Issue向け Slash Commands

- `/assign`
- `/block`
- `/done`
- `/handoff`
- `/plan`
- `/ready-for-review`
- `/start`
- `/unblock`

## PRコマンドで付与される静的ラベル

- `ci-non-blocking`
- `enforce-a11y`
- `enforce-bdd-lint`
- `enforce-context-pack`
- `enforce-contracts`
- `enforce-coverage`
- `enforce-formal`
- `enforce-lh`
- `enforce-perf`
- `enforce-typecov`
- `pr-summary:detailed`
- `pr-summary:digest`
- `qa-batch:agents`
- `qa-batch:cli`
- `qa-batch:commands`
- `qa-batch:property`
- `run-adapters`
- `run-cedar`
- `run-drift`
- `run-formal`
- `run-hermetic`
- `run-qa`
- `run-resilience`
- `run-security`
- `run-spec`

## Issueコマンドで付与される静的ラベル

- `status:blocked`
- `status:done`
- `status:in-progress`
- `status:review`

## 動的ラベルパターン

- `coverage:<0-100>`
- `handoff:agent-{a|b|c}`
- `lh:<0-100>`
- `perf:<0-100>`

## Source

- `.github/workflows/agent-commands.yml`
