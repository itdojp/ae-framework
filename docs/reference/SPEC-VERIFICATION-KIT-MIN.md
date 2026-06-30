---
docRole: ssot
lastVerified: '2026-07-01'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Spec & Verification Kit Minimum Activation Profile

## English

### Purpose
- Define the minimum TypeScript package that activates specification, tests, and verification from one local command.
- Keep the baseline executable without requiring every consumer to adopt BDD or authored property suites immediately.
- Make extension points explicit so Go or other languages can be added later without changing the TypeScript baseline.

### What is included
- BDD templates: `docs/templates/spec-kit/bdd-template.feature` and `docs/templates/spec-kit/bdd-steps.template.js`.
- Property template: `docs/templates/spec-kit/property-template.md` for authored `tests/property/**/*.test.ts` suites.
- Built-in property smoke: `pnpm run test:property`, backed by `scripts/testing/property-harness.mjs`.
- Baseline checks: `pnpm lint`, `pnpm types:check`, and `pnpm run test:fast`.
- One-command activation runner: `pnpm run spec-kit-min:verify`.
- Runnable traceable example: `examples/spec-verification-kit-min/`.
- CI template: `docs/templates/ci/spec-kit-min.workflow.yml`.
- Seed layout: `templates/spec-kit-min/`.

### One-command activation

Run the minimum profile from an ae-framework checkout:

```bash
pnpm run spec-kit-min:verify
```

This command runs the baseline checks and writes activation evidence:

- `artifacts/spec-kit-min/activation-summary.json`
- `artifacts/spec-kit-min/activation-summary.md`
- `artifacts/spec-kit-min/property-harness-summary.json` from the built-in property smoke check

The summary records each check, command, pass/fail state, discovered requirement
or `@trace:<id>` links, and the distinction between built-in harness checks and
authored custom suites.

### Running authored BDD/property suites

Custom suites are deliberately opt-in. This prevents the minimum activation path
from silently treating copied templates as mandatory product tests before a team
has completed the step definitions and generators.

```bash
pnpm run spec-kit-min:verify -- --run-custom-suites
```

With `--run-custom-suites`, the runner also executes:

- BDD examples discovered under `spec/bdd/**/*.feature` with step files under `spec/bdd/steps/`
- Property examples discovered under `tests/property/**/*.{test,spec}.{ts,js,mjs,cjs}`

If custom suites are discovered but `--run-custom-suites` is omitted, the summary
returns `warning` and explains that `property-smoke` is the built-in harness while
`property-custom` is the authored suite lane.

### Runnable example

Run only the example BDD/property suites:

```bash
pnpm run spec-kit-min:verify -- \
  --profile-root examples/spec-verification-kit-min \
  --run-custom-suites \
  --skip lint \
  --skip types \
  --skip fast \
  --skip property-smoke
```

The example includes:

- `requirements/minimum-profile.requirements.json` with `REQ-SVK-001`
- `spec/bdd/features/minimum-profile.feature` tagged with `@trace:REQ-SVK-001`
- `spec/bdd/steps/minimum-profile.steps.js`
- `tests/property/minimum-profile.property.test.ts` tagged with `@trace:REQ-SVK-001`
- `vitest.config.ts` scoped to the example property tests

### Failure and troubleshooting guide

| Symptom | Meaning | Fix |
| --- | --- | --- |
| `property-smoke` fails | The built-in property harness or `fast-check` wiring is broken. | Run the reproducible command from `artifacts/spec-kit-min/property-harness-summary.json`. |
| `property-custom` is `warning` | Authored property tests were discovered, but `--run-custom-suites` was not supplied. | Add `--run-custom-suites` when you are ready to execute authored suites. |
| `property-custom` fails | A custom `tests/property/**/*.test.ts` suite failed. | Inspect the Vitest output and the trace refs in `activation-summary.md`. |
| `bdd-custom` is `warning` | BDD features were discovered, but custom suites were not requested. | Add `--run-custom-suites`. |
| `bdd-custom` fails with missing steps | `.feature` files exist without matching JavaScript step files under `spec/bdd/steps/`. | Copy and complete `docs/templates/spec-kit/bdd-steps.template.js`. TypeScript step files require a separate loader and are intentionally not auto-imported by the minimum profile. |
| `lint`, `types`, or `fast` fails | Baseline repository checks failed. | Fix the reported ESLint, TypeScript, or fast-test failure before promoting the profile. |

### CI usage

Copy `docs/templates/ci/spec-kit-min.workflow.yml` into a consumer repository or
adapt its command in ae-framework. It uses the same activation runner so local and
CI evidence have the same shape.

### Extension points when adding Go
- Tests: `go test ./...`
- Property testing: evaluate `gopter` or `rapid`
- Lint: `golangci-lint run`
- Coordinate TypeScript and Go execution through a shared `Makefile`, `Taskfile`, or a future language-specific activation runner.

### Implementation status
- [x] Documentation-first BDD and property templates exist.
- [x] `templates/spec-kit-min/` provides the minimum seed layout.
- [x] `pnpm run spec-kit-min:verify` provides the executable activation command.
- [x] `examples/spec-verification-kit-min/` provides a runnable traceable fixture.
- [x] Activation summary artifacts tie checks to requirement/spec fragments when `@trace:<id>` or requirement files are present.
- [x] Custom suite discovery is distinct from the built-in property harness smoke check.

## 日本語

### 目的
- TypeScript を主軸に、仕様・テスト・検証を 1 コマンドで有効化できる最小セットを定義する。
- BDD や authored property suite をすべての利用者に即時強制せず、実行可能な baseline として維持する。
- Go などの追加言語は拡張ポイントとして残し、TypeScript baseline を再設計しない。

### 含める要素
- BDD template: `docs/templates/spec-kit/bdd-template.feature` と `docs/templates/spec-kit/bdd-steps.template.js`
- Property template: authored `tests/property/**/*.test.ts` 向けの `docs/templates/spec-kit/property-template.md`
- Built-in property smoke: `scripts/testing/property-harness.mjs` を使う `pnpm run test:property`
- Baseline checks: `pnpm lint`, `pnpm types:check`, `pnpm run test:fast`
- 1 コマンド activation runner: `pnpm run spec-kit-min:verify`
- trace 付き実行例: `examples/spec-verification-kit-min/`
- CI template: `docs/templates/ci/spec-kit-min.workflow.yml`
- Seed layout: `templates/spec-kit-min/`

### 1 コマンド activation

ae-framework checkout で以下を実行します。

```bash
pnpm run spec-kit-min:verify
```

このコマンドは baseline checks を実行し、以下の evidence を出力します。

- `artifacts/spec-kit-min/activation-summary.json`
- `artifacts/spec-kit-min/activation-summary.md`
- built-in property smoke の `artifacts/spec-kit-min/property-harness-summary.json`

summary には、各 check、実行 command、pass/fail、検出された requirement / `@trace:<id>` link、built-in harness と authored custom suite の区別が記録されます。

### authored BDD/property suite の実行

Custom suite は明示 opt-in です。これにより、コピー直後で未完成のテンプレートを mandatory product test と誤認しないようにします。

```bash
pnpm run spec-kit-min:verify -- --run-custom-suites
```

`--run-custom-suites` を付けると、runner は以下も実行します。

- `spec/bdd/**/*.feature` と `spec/bdd/steps/` 配下の step file
- `tests/property/**/*.{test,spec}.{ts,js,mjs,cjs}` の authored property example

Custom suite が検出されているのに `--run-custom-suites` がない場合、summary は `warning` になり、`property-smoke` が built-in harness、`property-custom` が authored suite lane であることを明示します。

### 実行可能 example

Example の BDD/property suite のみを実行する最小コマンドです。

```bash
pnpm run spec-kit-min:verify -- \
  --profile-root examples/spec-verification-kit-min \
  --run-custom-suites \
  --skip lint \
  --skip types \
  --skip fast \
  --skip property-smoke
```

Example には以下が含まれます。

- `requirements/minimum-profile.requirements.json` の `REQ-SVK-001`
- `@trace:REQ-SVK-001` 付きの `spec/bdd/features/minimum-profile.feature`
- `spec/bdd/steps/minimum-profile.steps.js`
- `@trace:REQ-SVK-001` 付きの `tests/property/minimum-profile.property.test.ts`
- example property test に限定した `vitest.config.ts`

### 失敗時の見方

| 症状 | 意味 | 対応 |
| --- | --- | --- |
| `property-smoke` が失敗 | built-in property harness または `fast-check` wiring が壊れている | `artifacts/spec-kit-min/property-harness-summary.json` の reproducible command を実行する |
| `property-custom` が `warning` | authored property tests は検出されたが `--run-custom-suites` がない | authored suite を実行する段階で `--run-custom-suites` を付ける |
| `property-custom` が失敗 | `tests/property/**/*.test.ts` の custom suite が失敗 | Vitest output と `activation-summary.md` の trace refs を確認する |
| `bdd-custom` が `warning` | BDD feature は検出されたが custom suite 実行が要求されていない | `--run-custom-suites` を付ける |
| `bdd-custom` が missing steps で失敗 | `.feature` に対応する JavaScript step file が `spec/bdd/steps/` にない | `docs/templates/spec-kit/bdd-steps.template.js` をコピーして完成させる。TypeScript step file は別 loader が必要なため minimum profile では自動 import しない |
| `lint`, `types`, `fast` が失敗 | baseline repository check が失敗 | ESLint / TypeScript / fast-test の出力を修正してから profile を昇格する |

### CI での利用

`docs/templates/ci/spec-kit-min.workflow.yml` を consumer repository にコピーするか、ae-framework 内で同等コマンドとして利用します。local と CI が同じ activation summary 形式を出すように、同じ runner を使います。

### Go 追加時の拡張ポイント
- Tests: `go test ./...`
- Property: `gopter` もしくは `rapid` を検討
- Lint: `golangci-lint run`
- TypeScript / Go の統合は `Makefile`、`Taskfile`、または将来の言語別 activation runner で扱う。

### 実装状況
- [x] Documentation-first BDD / property template が存在する
- [x] `templates/spec-kit-min/` が minimum seed layout を提供する
- [x] `pnpm run spec-kit-min:verify` が executable activation command を提供する
- [x] `examples/spec-verification-kit-min/` が trace 付き runnable fixture を提供する
- [x] Activation summary artifact が `@trace:<id>` / requirement file から check と requirement/spec fragment を接続する
- [x] Custom suite discovery と built-in property harness smoke check を区別して記録する
