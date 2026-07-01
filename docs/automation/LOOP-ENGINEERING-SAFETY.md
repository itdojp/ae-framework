---
docRole: ssot
lastVerified: '2026-07-01'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Loop Engineering Safety, Observability, and Budgets

> Language / 言語: English | 日本語

---

## English

This document defines the report-only safety profile for ae-framework loop engineering. It extends the first loop MVP in `docs/integrations/LOOP-ENGINEERING.md` with explicit budgets, stop rules, observability metrics, replay evidence, and privacy guidance before any higher-autonomy workflow is considered.

### Contracts and command surface

- Policy contract: `schema/loop-policy.schema.json`
- Input contract: `schema/loop-run-input.schema.json`
- Summary contract: `schema/loop-run-summary.schema.json`
- Runner: `scripts/loop/run-report-only.mjs`
- Package script: `pnpm -s run loop:run-report-only`
- Strict fixture policy: `fixtures/loop/strict-safety.loop-policy.json`
- Safety metrics fixture: `examples/loop-engineering/safety/loop-input.json`
- Safety summary fixture: `fixtures/loop/safety-budget.loop-run-summary.json`

Example safety-budget run:

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/safety/loop-input.json \
  --policy fixtures/loop/strict-safety.loop-policy.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/loop/safety-budget.loop-run-summary.json \
  --output-md artifacts/loop/safety-budget.loop-run-summary.md
```

### Policy fields

`loop-policy/v1` is intentionally narrow and report-only. It captures:

- `budgets.maxIterations`: hard cap for fixture iterations. The runner uses the lower value of input / CLI / policy max iterations.
- `budgets.wallClockBudgetSeconds`: fixture-observed elapsed-time budget. The runner records observed seconds and stops as `blocked` when exceeded.
- `budgets.modifiedFileLimit`: maximum modified-file references an action hook may claim. The default remains `0` for fixture-only runs.
- `commandPolicy.allowList` and `commandPolicy.denyList`: command prefixes/fragments that decide whether a validation command is permitted evidence.
- `pathPolicy.allowedPrefixes` and `pathPolicy.deniedPrefixes`: repository-relative path controls for raw output, evidence paths, and modified-file paths.
- `evidenceRequirements.requiredEvidenceIds`: required evidence IDs such as `ev.verify-lite` or `ev.human-approval`.
- `humanApproval.requiredRiskLevels`: risk levels that require approval evidence before the loop may continue.
- `stopRules.repeatedFailureThreshold`: the count at which the same `validation.failureSignature` becomes a thrashing signal.
- `privacy`: public raw-log posture and classes that must remain redacted or internal-only.

### Stop rules

The report-only runner can now stop on these policy conditions:

| Condition | Summary stop reason | Finding code |
| --- | --- | --- |
| Effective max iterations reached | `max-iterations` | `loop-policy-max-iterations` when policy lowered the cap |
| Denied command or command outside allow list | `unsafe-action` | `loop-policy-denied-command` / `loop-policy-command-not-allowed` |
| Denied path or path outside allow list | `unsafe-action` | `loop-policy-denied-path` / `loop-policy-path-not-allowed` |
| Missing required evidence | `blocked` | `loop-policy-missing-evidence` |
| High or critical risk without approval evidence | `human-required` | `loop-policy-human-approval-required` |
| Repeated failure signature at threshold | `blocked` | `loop-policy-repeated-failure` |
| Wall-clock budget exceeded | `blocked` | `loop-policy-wall-clock-budget` |
| Modified-file limit exceeded | `unsafe-action` | `loop-policy-modified-file-limit` |

The stop result is still evidence, not approval authority. Human review, branch protection, required checks, and repository policy remain authoritative.

### Observability metrics

New summaries produced by `scripts/loop/run-report-only.mjs` include `observability` and `replay` sections. The `loop-run-summary/v1` schema keeps these sections optional so stored summaries produced before loop-policy support remain valid during migration.

- `verificationSequence`: pass/fail/warn/not-run sequence across executed iterations.
- `elapsedSecondsObserved`: sum of fixture-observed elapsed seconds.
- `blockedToActionable`: fixture-provided time from blocked evidence to an actionable next step, or `not_collected`.
- `repeatedFailureSignatures`: repeated `validation.failureSignature` values with first/last iteration IDs.
- `unsafeActionStops`, `missingEvidenceIds`, `deniedCommands`, `deniedPaths`, `modifiedFileCount`, and `highRiskEscalations`.
- `approvalAuthority`: fixed report-only statement that loop output does not replace human approval or required checks.
- `replay.inputHash`, `replay.policyHash`, and `replay.idempotencyKey` for deterministic fixture replay.

### Idempotency and replay guidance

For deterministic replay, keep all of the following stable:

1. `loop-run-input/v1` file content.
2. `loop-policy/v1` file content or the embedded default policy.
3. `--generated-at` value.
4. Repository-relative fixture evidence paths.

If any of these inputs changes, treat the new `idempotencyKey` as a different run. Do not compare raw timestamps or absolute local paths across worktrees; compare normalized report paths and hashes.

### Redaction and privacy guidance

- Public artifacts should default to metadata-only evidence. Store raw prompts, raw hosted-LLM output, secrets, tokens, and customer data outside public loop summaries.
- Use `validation.rawOutputPath` for redacted or synthetic fixture outputs only.
- If a live pilot later needs raw logs, record the redaction policy and review owner before publication.
- Do not paste sensitive raw commands or raw logs into PR comments; paste `reviewSurface.body` or the Markdown summary after confirming it contains only allowed metadata.

### Report-only versus future enforcement

This slice adds no blocking policy-gate condition. Promotion to enforcement requires a future issue that states:

1. Which finding codes become blocking.
2. Which labels or assurance profiles activate enforcement.
3. How false positives are waived and audited.
4. Which artifacts become required in branch protection.
5. How rollback is performed if loop safety checks block legitimate work.

## 日本語

このドキュメントは ae-framework loop engineering の report-only safety profile を定義します。最初の loop MVP（`docs/integrations/LOOP-ENGINEERING.md`）に対して、より高い自律性を検討する前に、budget、stop rule、observability metrics、replay evidence、privacy guidance を追加します。

### 契約とコマンド

- policy contract: `schema/loop-policy.schema.json`
- input contract: `schema/loop-run-input.schema.json`
- summary contract: `schema/loop-run-summary.schema.json`
- runner: `scripts/loop/run-report-only.mjs`
- package script: `pnpm -s run loop:run-report-only`
- strict fixture policy: `fixtures/loop/strict-safety.loop-policy.json`
- safety metrics fixture: `examples/loop-engineering/safety/loop-input.json`
- safety summary fixture: `fixtures/loop/safety-budget.loop-run-summary.json`

safety-budget 実行例:

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/safety/loop-input.json \
  --policy fixtures/loop/strict-safety.loop-policy.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/loop/safety-budget.loop-run-summary.json \
  --output-md artifacts/loop/safety-budget.loop-run-summary.md
```

### policy fields

`loop-policy/v1` は意図的に narrow かつ report-only です。次を記録します。

- `budgets.maxIterations`: fixture iteration の上限。runner は input / CLI / policy の最小値を使います。
- `budgets.wallClockBudgetSeconds`: fixture が観測した elapsed time の budget。超過時は `blocked` で停止します。
- `budgets.modifiedFileLimit`: action hook が主張できる modified-file reference の上限。fixture-only 既定値は `0` です。
- `commandPolicy.allowList` / `commandPolicy.denyList`: validation command を許可または拒否する prefix / fragment。
- `pathPolicy.allowedPrefixes` / `pathPolicy.deniedPrefixes`: raw output、evidence path、modified-file path に対する repository-relative path control。
- `evidenceRequirements.requiredEvidenceIds`: `ev.verify-lite` や `ev.human-approval` などの必須 evidence ID。
- `humanApproval.requiredRiskLevels`: loop 継続前に approval evidence を必要とする risk level。
- `stopRules.repeatedFailureThreshold`: 同一 `validation.failureSignature` を thrashing signal とみなす回数。
- `privacy`: public raw-log posture と、redacted / internal-only にすべき情報クラス。

### stop rules

report-only runner は次の policy condition で停止できます。

| condition | summary stop reason | finding code |
| --- | --- | --- |
| effective max iterations 到達 | `max-iterations` | policy が上限を下げた場合 `loop-policy-max-iterations` |
| denied command または allow list 外 command | `unsafe-action` | `loop-policy-denied-command` / `loop-policy-command-not-allowed` |
| denied path または allow list 外 path | `unsafe-action` | `loop-policy-denied-path` / `loop-policy-path-not-allowed` |
| required evidence missing | `blocked` | `loop-policy-missing-evidence` |
| high / critical risk かつ approval evidence なし | `human-required` | `loop-policy-human-approval-required` |
| repeated failure signature が threshold 到達 | `blocked` | `loop-policy-repeated-failure` |
| wall-clock budget 超過 | `blocked` | `loop-policy-wall-clock-budget` |
| modified-file limit 超過 | `unsafe-action` | `loop-policy-modified-file-limit` |

stop result は証跡であり、承認権限ではありません。human review、branch protection、required checks、repository policy が引き続き authoritative です。

### observability metrics

`scripts/loop/run-report-only.mjs` が生成する新しい summary は `observability` と `replay` を含みます。`loop-run-summary/v1` schema では、loop-policy support 以前に生成された stored summary との互換性を維持するため、これらの section を optional とします。

- `verificationSequence`: 実行済み iteration の pass/fail/warn/not-run sequence。
- `elapsedSecondsObserved`: fixture が観測した elapsed seconds の合計。
- `blockedToActionable`: blocked evidence から actionable next step までの fixture-provided time。未収集なら `not_collected`。
- `repeatedFailureSignatures`: repeated `validation.failureSignature` と first/last iteration ID。
- `unsafeActionStops`、`missingEvidenceIds`、`deniedCommands`、`deniedPaths`、`modifiedFileCount`、`highRiskEscalations`。
- `approvalAuthority`: loop output が human approval / required checks を置換しないことを示す固定文。
- deterministic fixture replay 用の `replay.inputHash`、`replay.policyHash`、`replay.idempotencyKey`。

### idempotency と replay guidance

deterministic replay では次を固定します。

1. `loop-run-input/v1` file content。
2. `loop-policy/v1` file content または embedded default policy。
3. `--generated-at` value。
4. repository-relative fixture evidence path。

これらの入力が変わる場合は、新しい `idempotencyKey` を別 run として扱います。worktree 間では raw timestamp や absolute local path ではなく、normalized report path と hash を比較してください。

### redaction / privacy guidance

- public artifact は metadata-only evidence を既定にする。raw prompt、raw hosted-LLM output、secret、token、customer data は public loop summary に保存しない。
- `validation.rawOutputPath` は redacted または synthetic fixture output に限定する。
- live pilot で raw log が必要な場合は、公開前に redaction policy と review owner を記録する。
- PR comment に sensitive raw command / raw log を貼らない。許可済み metadata のみであることを確認してから `reviewSurface.body` または Markdown summary を貼る。

### report-only と将来の enforcement

この slice は blocking policy-gate condition を追加しません。enforcement へ昇格する場合は、将来の Issue で次を明示します。

1. blocking にする finding code。
2. enforcement を有効化する label または assurance profile。
3. false positive の waiver と audit 方法。
4. branch protection で required にする artifact。
5. loop safety check が正当な作業を block した場合の rollback 方法。
