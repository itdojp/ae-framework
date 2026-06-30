---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- docs/reference/EXEC-PLAN-V2.md
- schema/spec-kit-bridge-report.schema.json
lastVerified: '2026-06-30'
verificationCommand: pnpm -s run spec-kit:import-feature -- --generated-at 2026-06-30T00:00:00.000Z
---
# Spec Kit Bridge

> Language / 言語: English | 日本語

---

## English

The Spec Kit bridge is an optional, report-only interoperability path between GitHub Spec Kit artifacts and ae-framework assurance inputs. It does not vendor, fork, or execute Spec Kit. It reads local Spec Kit-style files and emits ae-framework-compatible artifacts for review:

- `artifacts/spec-kit/spec-kit-bridge-report.json` using `schema/spec-kit-bridge-report.schema.json`;
- `artifacts/spec-kit/spec-kit-bridge-report.md` for human review;
- `artifacts/spec-kit/context-pack.import.json` using `schema/context-pack-v1.schema.json`;
- `artifacts/spec-kit/exec-plan.v2.json` using `schema/exec-plan.v2.schema.json`.

The bridge is intended for teams that already use Spec Kit's constitution / specify / plan / tasks workflow and want ae-framework to remain the assurance control plane.

## Supported input layout

The importer expects a feature directory shaped like a Spec Kit feature:

| File role | Expected location in a Spec Kit feature |
| --- | --- |
| Constitution | project-local `.specify` memory directory |
| Feature specification | selected feature directory |
| Implementation plan | selected feature directory |
| Task list | selected feature directory |
| Interface contracts | selected feature directory's contracts subdirectory |
| Research notes | selected feature directory, optional |
| Data model | selected feature directory, optional |
| Quickstart | selected feature directory, optional |

The constitution file is resolved from the nearest project-local Spec Kit memory directory between the feature directory and repository root. This keeps fixture projects under `fixtures/spec-kit/*` usable without creating a repository-root `.specify` directory.

## Import command

Default greenfield fixture:

```bash
pnpm run spec-kit:import-feature -- --generated-at 2026-06-30T00:00:00.000Z
```

Import a real feature directory:

```bash
pnpm run spec-kit:import-feature -- \
  --feature-dir specs/001-my-feature \
  --output-dir artifacts/spec-kit
```

Useful options:

| Option | Purpose |
| --- | --- |
| `--feature-dir <path>` | Spec Kit feature directory. |
| `--project-root <path>` / `--work <path>` | Root for relative paths and `.specify` discovery. |
| `--output-dir <path>` | Directory for report, Context Pack import, and ExecPlan v2 import artifacts. |
| `--report-json`, `--report-md` | Override report output paths. |
| `--context-pack-json` | Override generated Context Pack path. |
| `--exec-plan-json` | Override generated ExecPlan v2 path. |
| `--generated-at <iso-date>` | Deterministic timestamp for fixtures or regression tests. |
| `--no-write` | Build and validate the mapping in memory without writing outputs. |

`result=warning` exits successfully. Warnings are expected for ordinary brownfield cases such as missing `contracts/*` or a task line without a `[US#]` marker. `result=fail` is reserved for unrecoverable input problems such as an unreadable feature directory.

## Mapping model

| Spec Kit source | ae-framework target | Notes |
| --- | --- | --- |
| Spec Kit constitution | Context Pack `forbidden_changes` / ExecPlan source refs | The bridge records governance context but does not enforce Spec Kit rules. |
| Functional requirements in the feature specification | Context Pack `acceptance_tests[]` and bridge report mappings | `FR-###` IDs become `AT-FR-###` anchors. |
| User stories in the feature specification | Context Pack `morphisms[]` and `AT-US#` acceptance anchors | Acceptance scenarios are preserved when present. |
| Technical context in the implementation plan | Context Pack `coding_conventions` and ExecPlan verification profile notes | Ambiguous or missing fields are recorded as report-only gaps. |
| Generated task list | ExecPlan v2 `taskGraph.nodes[]` and bridge report mappings | `T###` IDs become `task.t###` nodes. `[US#]` markers improve confidence. |
| `contracts/*` | ExecPlan `context.specKitRefs[]` and bridge report contract mappings | OpenAPI/YAML/JSON/Markdown contracts are classified but not executed. |

## Unsupported and lossy mappings

The bridge deliberately does not map or execute these fields:

- Spec Kit command hook side effects;
- task-to-issues GitHub issue creation;
- agent-specific slash-command invocation modes;
- free-form task prose beyond the preserved source line and phase;
- policy-gate enforcement based on bridge findings.

Lossy or ambiguous mappings are explicit in `unsupportedFields[]`, `findings[]`, and summary counts. They remain report-only until a separate policy issue promotes a specific finding class.

## Export guidance: ae-framework to Spec Kit

This issue adds import automation and export guidance, not a separate exporter. To start a Spec Kit feature from ae-framework inputs:

1. Use the Issue or Context Pack goal as the feature-specification summary.
2. Convert Context Pack `acceptance_tests[]` into Spec Kit acceptance scenarios.
3. Convert Context Pack objects and morphisms into the `Key Entities` and user-story sections.
4. Copy ExecPlan v2 `verificationProfile.commands[]` into implementation-plan validation notes.
5. Convert ExecPlan v2 `taskGraph.nodes[]` into `T###` task-list entries, keeping `dependsOn` as phase ordering notes.
6. Record ae-framework schemas or API contracts under `contracts/*` instead of embedding them into prose.
7. Run `pnpm run spec-kit:import-feature` after Spec Kit artifacts are authored to confirm round-trip traceability.

## Fixtures

| Fixture | Purpose |
| --- | --- |
| `fixtures/spec-kit/greenfield/` | Complete greenfield feature with constitution, spec, plan, tasks, contracts, research, and quickstart. Expected bridge result: `pass`. |
| `fixtures/spec-kit/brownfield/` | Brownfield modernization feature with missing contracts and one task without `[US#]`. Expected bridge result: `warning`. |
| `fixtures/spec-kit/*/expected/spec-kit-bridge-report.json` | Schema-validated report fixtures. |
| `fixtures/spec-kit/*/expected/context-pack.import.json` | Context Pack import fixtures. |
| `fixtures/spec-kit/*/expected/exec-plan.v2.json` | ExecPlan v2 import fixtures. |

## Verification

```bash
pnpm run spec-kit:import-feature -- --generated-at 2026-06-30T00:00:00.000Z
node scripts/context-pack/validate.mjs --sources artifacts/spec-kit/context-pack.import.json
pnpm run exec-plan:v2:validate -- --file artifacts/spec-kit/exec-plan.v2.json
node scripts/ci/validate-json.mjs
pnpm -s exec vitest run tests/scripts/spec-kit-bridge.test.ts --reporter dot
```

---

## 日本語

Spec Kit bridge は、GitHub Spec Kit の artifact を ae-framework の Context Pack / ExecPlan v2 / evidence contract に接続する optional かつ report-only の連携層です。Spec Kit を vendor / fork / 実行せず、ローカルの Spec Kit 形式ファイルを読み取り、review 用の ae-framework artifact を生成します。

主な方針は次の通りです。

- 通常の ae-framework 利用に Spec Kit を必須化しない。
- bridge finding は `warning` でも成功終了し、通常利用を止めない。
- policy-gate の enforcement へ昇格する場合は、別 Issue で対象 finding と rollback を定義する。
- feature specification、implementation plan、task list、contracts directory の参照を Context Pack と ExecPlan v2 に残し、PR review の traceability を高める。

最小実行例:

```bash
pnpm run spec-kit:import-feature -- \
  --feature-dir specs/001-my-feature \
  --output-dir artifacts/spec-kit
```

生成物は `artifacts/spec-kit/` 配下の JSON/Markdown です。Context Pack と ExecPlan v2 は既存の schema validation で確認し、bridge report は `schema/spec-kit-bridge-report.schema.json` で検証します。
