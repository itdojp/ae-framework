---
docRole: ssot
lastVerified: '2026-07-01'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Report-only Loop Engineering MVP

> Language / 言語: English | 日本語

---

## English

This document defines the first loop engineering surface for ae-framework. The MVP is deliberately report-only: it can plan from an Issue/ExecPlan v2 input, observe fixture evidence, evaluate validation status, and propose a next operator action, but it cannot merge, approve, push, or bypass review.

### Contract and command

- Input contract: `schema/loop-run-input.schema.json`
- Summary contract: `schema/loop-run-summary.schema.json`
- Safety policy contract: `schema/loop-policy.schema.json`
- Runner: `scripts/loop/run-report-only.mjs`
- Package script: `pnpm -s run loop:run-report-only`
- Fixture demo: `examples/loop-engineering/`
- Golden summaries: `fixtures/loop/`
- Safety and observability policy: `docs/automation/LOOP-ENGINEERING-SAFETY.md`

Default run:

```bash no-doctest
pnpm -s run loop:run-report-only
```

Deterministic success fixture:

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/success/loop-input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/loop/loop-run-summary.json \
  --output-md artifacts/loop/loop-run-summary.md
```

### Operator workflow

1. Start from an Issue, Context Pack references, and an ExecPlan v2 path.
2. Encode the safe fixture input in `loop-run-input/v1` shape and keep referenced paths inside the current working directory.
3. Run `loop:run-report-only` in a dedicated worktree or fixture-only mode.
4. Inspect `result`, `stopReason`, `iterations[].validation.command`, `iterations[].observedEvidence`, and `nextRecommendedAction`.
5. Inspect `policy`, `observability`, and `replay` when a `loop-policy/v1` file or the embedded default policy influenced the stop reason.
6. Paste `reviewSurface.body` or the Markdown summary into the PR/Issue when human review is needed.
7. Do not treat the loop summary as approval. Required checks, reviews, and repository policy remain authoritative.

### Stop reasons

The MVP uses these explicit stop reasons:

| Stop reason | Meaning | Process status |
| --- | --- | --- |
| `success` | Fixture verification reached the intended end state. | `0` |
| `blocked` | Evidence indicates the operator must inspect or adjust the plan. | `0` |
| `max-iterations` | The run reached the configured iteration limit. | `0` |
| `validation-failed` | A fixture marked `continue` despite validation status mismatch. | non-zero |
| `unsafe-action` | The input requested forbidden mutation, hosted LLM call, merge, push, or equivalent action. | non-zero |
| `human-required` | The fixture explicitly requires human judgement before continuing. | `0` |

### Limitations

- No hosted LLM calls are made by the runner or tests.
- No automatic merge, approval, review bypass, branch deletion, or commit push is supported.
- Validation commands are recorded as evidence commands; fixture mode does not execute them.
- The contract is a preview/report-only evidence surface. Later issues may connect it to stricter orchestration, but this MVP does not add a policy-gate blocking rule.
- Path handling is limited to the current working directory. The runner validates input and output schemas, normalizes embedded artifact paths to repository-relative form, and rejects output symlinks to avoid writing summaries through an unexpected filesystem route.
- Safety budgets, command/path policies, repeated-failure detection, redaction guidance, and replay hashes are defined in `docs/automation/LOOP-ENGINEERING-SAFETY.md`. These controls remain report-only in this slice.

## 日本語

このドキュメントは ae-framework の最初の loop engineering surface を定義します。MVP は意図的に report-only です。Issue / ExecPlan v2 入力から計画し、fixture evidence を観測し、検証状態を評価し、次の operator action を提案できます。ただし、merge、approve、push、review bypass は行えません。

### 契約とコマンド

- input contract: `schema/loop-run-input.schema.json`
- summary contract: `schema/loop-run-summary.schema.json`
- safety policy contract: `schema/loop-policy.schema.json`
- runner: `scripts/loop/run-report-only.mjs`
- package script: `pnpm -s run loop:run-report-only`
- fixture demo: `examples/loop-engineering/`
- golden summaries: `fixtures/loop/`
- safety and observability policy: `docs/automation/LOOP-ENGINEERING-SAFETY.md`

既定実行:

```bash no-doctest
pnpm -s run loop:run-report-only
```

deterministic success fixture:

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/success/loop-input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/loop/loop-run-summary.json \
  --output-md artifacts/loop/loop-run-summary.md
```

### operator workflow

1. Issue、Context Pack references、ExecPlan v2 path から開始する。
2. 安全な fixture input を `loop-run-input/v1` 形状で記述し、参照パスを current working directory 内に保つ。
3. 専用 worktree または fixture-only mode で `loop:run-report-only` を実行する。
4. `result`、`stopReason`、`iterations[].validation.command`、`iterations[].observedEvidence`、`nextRecommendedAction` を確認する。
5. `loop-policy/v1` file または embedded default policy が stop reason に影響した場合は、`policy`、`observability`、`replay` を確認する。
6. human review が必要な場合は、`reviewSurface.body` または Markdown summary を PR / Issue に貼る。
7. loop summary を承認として扱わない。required checks、reviews、repository policy が引き続き authoritative evidence である。

### stop reasons

MVP は次の明示的 stop reason を使います。

| stop reason | 意味 | process status |
| --- | --- | --- |
| `success` | fixture verification が意図した終了状態に到達した。 | `0` |
| `blocked` | operator が plan を確認または修正する必要がある。 | `0` |
| `max-iterations` | 設定された iteration limit に到達した。 | `0` |
| `validation-failed` | validation status mismatch があるのに fixture が `continue` を指定した。 | non-zero |
| `unsafe-action` | mutation、hosted LLM call、merge、push、相当する forbidden action が要求された。 | non-zero |
| `human-required` | 継続前に人間の判断が必要である。 | `0` |

### limitations

- runner / tests は hosted LLM API を呼び出さない。
- automatic merge、approval、review bypass、branch deletion、commit push はサポートしない。
- validation command は evidence command として記録する。fixture mode では実行しない。
- 契約は preview/report-only evidence surface である。後続 Issue で stricter orchestration に接続する可能性はあるが、この MVP は policy-gate blocking rule を追加しない。
- path handling は current working directory に限定する。runner は input / output schema を検証し、埋め込み artifact path を repository-relative 形式へ正規化し、summary が予期しない filesystem route に書き込まれないよう symlink output file を拒否する。
- safety budget、command/path policy、repeated-failure detection、redaction guidance、replay hash は `docs/automation/LOOP-ENGINEERING-SAFETY.md` で定義する。この slice では report-only のままである。
