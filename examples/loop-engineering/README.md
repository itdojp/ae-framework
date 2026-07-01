---
docRole: derived
canonicalSource:
- docs/integrations/LOOP-ENGINEERING.md
- docs/automation/LOOP-ENGINEERING-SAFETY.md
- schema/loop-policy.schema.json
- schema/loop-run-input.schema.json
- schema/loop-run-summary.schema.json
- scripts/loop/run-report-only.mjs
lastVerified: '2026-07-01'
---
# Report-only loop engineering example

> Language / 言語: English | 日本語

## English

This example demonstrates the Issue #3552 loop engineering MVP. It is fixture-backed and offline: the runner reads `loop-input.json`, records the validation command and observed evidence, then emits a report-only summary for operator review.

The input fixtures validate against `schema/loop-run-input.schema.json`; generated summaries validate against `schema/loop-run-summary.schema.json`. Safety budgets validate against `schema/loop-policy.schema.json`.

### Success path

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/success/loop-input.json \
  --generated-at 2026-07-01T00:00:00.000Z
```

Expected fixture artifacts:

- `fixtures/loop/success.loop-run-summary.json`
- `fixtures/loop/success.loop-run-summary.md`

### Blocked path

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/blocked/loop-input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/loop/blocked-loop-run-summary.json \
  --output-md artifacts/loop/blocked-loop-run-summary.md
```

`blocked` remains a report-only operator outcome. The command exits successfully so the generated summary can be posted to a PR or Issue for human review. Unsafe actions and validation-status mismatches use a non-zero process status.

### Safety-budget path

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/safety/loop-input.json \
  --policy fixtures/loop/strict-safety.loop-policy.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/loop/safety-budget.loop-run-summary.json \
  --output-md artifacts/loop/safety-budget.loop-run-summary.md
```

Expected fixture artifacts:

- `fixtures/loop/safety-budget.loop-run-summary.json`
- `fixtures/loop/safety-budget.loop-run-summary.md`

The safety fixture records repeated failure signatures, blocked-to-actionable timing, replay hashes, and the report-only approval boundary. The repeated signature stops as `blocked`; it does not approve or merge anything.

### Safety boundaries

- The demo does not call hosted LLM APIs.
- The demo does not merge PRs, push commits, or approve reviews.
- `actionHook.mutatesRepository=true` is treated as unsafe unless the fixture explicitly allows mutations.
- The summary records every validation command and observed evidence path used by the iteration.
- `loop-policy/v1` can deny commands/paths, require evidence, cap iterations, require human approval for high-risk runs, and expose repeated-failure thrashing signals.

## 日本語

この例は Issue #3552 の loop engineering MVP です。fixture-backed かつ offline で動作します。runner は `loop-input.json` を読み、検証コマンドと観測証跡を記録し、operator review 向けの report-only summary を出力します。

input fixture は `schema/loop-run-input.schema.json`、生成 summary は `schema/loop-run-summary.schema.json` で検証されます。safety budget は `schema/loop-policy.schema.json` で検証されます。

### success path

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/success/loop-input.json \
  --generated-at 2026-07-01T00:00:00.000Z
```

期待 fixture artifact:

- `fixtures/loop/success.loop-run-summary.json`
- `fixtures/loop/success.loop-run-summary.md`

### blocked path

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/blocked/loop-input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/loop/blocked-loop-run-summary.json \
  --output-md artifacts/loop/blocked-loop-run-summary.md
```

`blocked` は report-only の運用結果です。生成された summary を PR / Issue に貼れるよう、コマンド自体は成功終了します。unsafe action と validation status mismatch は non-zero status を返します。

### safety-budget path

```bash no-doctest
pnpm -s run loop:run-report-only -- \
  --input examples/loop-engineering/safety/loop-input.json \
  --policy fixtures/loop/strict-safety.loop-policy.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/loop/safety-budget.loop-run-summary.json \
  --output-md artifacts/loop/safety-budget.loop-run-summary.md
```

期待 fixture artifact:

- `fixtures/loop/safety-budget.loop-run-summary.json`
- `fixtures/loop/safety-budget.loop-run-summary.md`

safety fixture は repeated failure signature、blocked-to-actionable timing、replay hash、report-only approval boundary を記録します。repeated signature は `blocked` として停止しますが、承認や merge は行いません。

### safety boundary

- hosted LLM API は呼び出さない。
- PR merge、commit push、review approval は行わない。
- `actionHook.mutatesRepository=true` は、fixture が明示的に mutation を許可しない限り unsafe として扱う。
- 各 iteration は、使用した validation command と observed evidence path を summary に記録する。
- `loop-policy/v1` は command/path deny、required evidence、iteration cap、high-risk run の human approval requirement、repeated-failure thrashing signal を report-only で可視化できる。
