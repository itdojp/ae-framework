---
docRole: derived
canonicalSource:
- package.json
- docs/testing/test-categorization.md
- docs/testing/parallel-execution-strategy.md
- docs/ci/label-gating.md
- docs/quality/coverage-policy.md
lastVerified: '2026-05-08'
---
# Testing Portfolio and Coverage Baseline Operations

> Language / 言語: English | 日本語

---

## English

### Purpose

Use this index to choose the smallest test lane that gives adequate signal for the change under review. The canonical script names remain in `package.json`; this document routes contributors to those scripts and to the CI labels that opt into heavier lanes.

### Recommended command routes

| Context | Primary command(s) | Cost class | Use when |
| --- | --- | --- | --- |
| Local edit loop | `pnpm run test:fast`, focused `vitest run <path>` | S | Validating a small source or test change before commit. |
| Local unit / contract confidence | `pnpm run test:unit`, `pnpm run test:contracts` | S-M | Updating core modules, schemas, CLI helpers, or contract fixtures. |
| PR baseline | `pnpm run verify:lite` or `pnpm run test:ci:lite` | M | Preparing a PR that should match the default required-check posture. |
| Coverage inspection | `pnpm run coverage` | M-L | Refreshing coverage evidence or validating `coverage-check` behavior. |
| Extended PR signal | `pnpm run test:ci:extended` | L | High-risk changes, integration-sensitive edits, or label-gated PR runs. |
| Nightly / scheduled heavy signal | `pnpm run test:mbt:ci`, `pnpm run pipelines:mutation:quick`, `pnpm run verify:formal` | XL | Regression discovery, assurance refresh, or scheduled quality reporting. |
| Release readiness | `pnpm run verify:lite`, `pnpm run test:ci:extended`, selected heavy lanes | L-XL | Confirming the release candidate across default and opt-in lanes. |

Cost classes are approximate: S is usually suitable for the local edit loop, M for pre-PR checks, L for extended CI or pre-release runs, and XL for scheduled or explicitly requested assurance lanes.

### Category selection criteria

| Category | Representative command(s) | Choose this when | CI label / control |
| --- | --- | --- | --- |
| Unit | `pnpm run test:fast`, `pnpm run test:unit` | The change is isolated to functions, adapters, utilities, or small command helpers. | Default `verify-lite` path; no special label. |
| Contract | `pnpm run test:contracts` | JSON schema, artifact shape, CLI output, or compatibility contracts changed. | `enforce-artifacts` for blocking artifact validation when appropriate. |
| Property | `pnpm run test:property`, `pnpm run pbt` | Invariants, parsers, normalizers, generators, or boundary-heavy logic changed. | `run-property`; `enforce-testing` can make related checks blocking. |
| Model-based (MBT) | `pnpm run test:mbt`, `pnpm run test:mbt:ci` | Stateful flows, trace transitions, or workflow behavior changed. | `run-mbt`. |
| Mutation | `pnpm run mutation`, `pnpm run pipelines:mutation:quick` | The risk is weak assertions or insufficient negative-path coverage. | `run-mutation`. |
| Formal | `pnpm run verify:formal` | A formal spec, model, trace contract, or high-assurance invariant changed. | Usually scheduled/manual; pair with high-risk review labels as needed. |
| Security | `pnpm run test:security-assurance`, `pnpm run security:integrated:quick`, `pnpm run security:integrated:full` | Security findings, SBOM, dependency, claim extraction, or assurance-lane evidence changed. | `run-security` for security/SBOM workflows. |
| Coverage | `pnpm run coverage` | The change affects the coverage baseline or coverage reporting path. | `enforce-coverage`; `coverage:<pct>` for threshold override. |
| Extended CI | `pnpm run test:ci:extended` | The PR needs integration, property, MBT, or mutation lanes beyond the default baseline. | `run-ci-extended`, plus narrower labels such as `run-property`, `run-mbt`, `run-mutation`. |

### CI label map

| Label | Effect | Typical use |
| --- | --- | --- |
| `run-ci-extended` | Starts the heavy CI Extended lane. | Broad high-risk PRs or release-candidate validation. |
| `run-mbt` | Starts the MBT smoke portion of CI Extended. | Stateful workflow or trace-transition changes. |
| `run-mutation` | Starts mutation auto-diff / scoped mutation work. | Assertion-strength or negative-path validation. |
| `run-property` | Starts the property-harness portion of CI Extended. | Parser, normalizer, generator, or invariant-heavy changes. |
| `enforce-coverage` | Makes coverage threshold enforcement blocking. | Coverage-sensitive PRs after the report-only baseline is understood. |

See `docs/ci/label-gating.md` for the broader label policy.

### Coverage baseline and artifact treatment

- The project coverage command is `pnpm run coverage`; it emits `coverage/coverage-summary.json` and `coverage/lcov.info` through Vitest reporters.
- `coverage/` is ignored by `.gitignore`, so coverage output is treated as a generated artifact, not as a manually maintained tracked baseline.
- Documentation may record the latest observed baseline for operational context, but the current baseline is established by rerunning the command on the target commit.
- On hosts without a detectable Docker or Podman engine, the non-CI command can fail in `tests/container/container-agent.test.ts`. For local baseline emulation of CI degraded-mode behavior, use `CI=1 pnpm run coverage` and record that environment in the evidence.

Latest observed baseline on `origin/main` `944fc818dd89a9d51cb72f1c2ee6e1b5cfa3e7e1` (2026-05-08, `CI=1 pnpm -s run coverage`):

| Metric | Percent | Covered / Total |
| --- | ---: | ---: |
| Lines | 31.96% | 53,302 / 166,738 |
| Statements | 31.96% | 53,302 / 166,738 |
| Functions | 60.76% | 3,132 / 5,154 |
| Branches | 67.89% | 10,708 / 15,771 |

### Verification for docs-only updates

Run the same documentation and type-surface checks used by the planning issue:

- `pnpm -s run check:doc-consistency`
- `pnpm -s run check:doc-todo-markers`
- `pnpm -s run check:runbook-command-blocks`
- `pnpm -s run types:check`

## 日本語

### 目的

この index は、変更内容に対して十分な signal を得られる最小の test lane を選ぶための入口です。script 名の一次情報は `package.json` に置き、この文書では各 script と heavy lane を起動する CI label への導線を整理します。

### 推奨コマンド経路

| 文脈 | 代表コマンド | Cost class | 利用場面 |
| --- | --- | --- | --- |
| Local edit loop | `pnpm run test:fast`, focused `vitest run <path>` | S | 小さい source / test 変更を commit 前に確認する場合。 |
| Local unit / contract confidence | `pnpm run test:unit`, `pnpm run test:contracts` | S-M | core module、schema、CLI helper、contract fixture を更新した場合。 |
| PR baseline | `pnpm run verify:lite` または `pnpm run test:ci:lite` | M | 既定の required-check posture に合わせて PR を準備する場合。 |
| Coverage inspection | `pnpm run coverage` | M-L | coverage evidence や `coverage-check` の挙動を確認する場合。 |
| Extended PR signal | `pnpm run test:ci:extended` | L | high-risk 変更、integration-sensitive な変更、label-gated PR run が必要な場合。 |
| Nightly / scheduled heavy signal | `pnpm run test:mbt:ci`, `pnpm run pipelines:mutation:quick`, `pnpm run verify:formal` | XL | regression discovery、assurance refresh、scheduled quality reporting。 |
| Release readiness | `pnpm run verify:lite`, `pnpm run test:ci:extended`, selected heavy lanes | L-XL | release candidate を default lane と opt-in lane の両方で確認する場合。 |

Cost class は目安です。S は local edit loop、M は pre-PR、L は extended CI / pre-release、XL は scheduled run または明示依頼された assurance lane を想定します。

### カテゴリ選択基準

| Category | 代表コマンド | 選択する場面 | CI label / control |
| --- | --- | --- | --- |
| Unit | `pnpm run test:fast`, `pnpm run test:unit` | 関数、adapter、utility、小さい command helper の変更。 | 既定の `verify-lite` 経路。特別な label は不要。 |
| Contract | `pnpm run test:contracts` | JSON schema、artifact shape、CLI output、compatibility contract の変更。 | 必要に応じて `enforce-artifacts` で artifact validation を blocking 化。 |
| Property | `pnpm run test:property`, `pnpm run pbt` | invariant、parser、normalizer、generator、境界値の多い logic の変更。 | `run-property`; 関連 check の blocking 化は `enforce-testing`。 |
| Model-based (MBT) | `pnpm run test:mbt`, `pnpm run test:mbt:ci` | stateful flow、trace transition、workflow behavior の変更。 | `run-mbt`. |
| Mutation | `pnpm run mutation`, `pnpm run pipelines:mutation:quick` | assertion の弱さや negative path coverage を確認したい場合。 | `run-mutation`. |
| Formal | `pnpm run verify:formal` | formal spec、model、trace contract、high-assurance invariant の変更。 | 通常は scheduled / manual。必要に応じて high-risk review label と組み合わせる。 |
| Security | `pnpm run test:security-assurance`, `pnpm run security:integrated:quick`, `pnpm run security:integrated:full` | security finding、SBOM、dependency、claim extraction、assurance-lane evidence の変更。 | Security / SBOM workflow は `run-security`。 |
| Coverage | `pnpm run coverage` | coverage baseline または coverage reporting path に影響する変更。 | `enforce-coverage`; しきい値 override は `coverage:<pct>`。 |
| Extended CI | `pnpm run test:ci:extended` | 既定 baseline を超えて integration、property、MBT、mutation lane の signal が必要な PR。 | `run-ci-extended`, 追加で `run-property`, `run-mbt`, `run-mutation`。 |

### CI label map

| Label | 効果 | 典型的な利用場面 |
| --- | --- | --- |
| `run-ci-extended` | heavy CI Extended lane を起動する。 | 広範な high-risk PR または release-candidate validation。 |
| `run-mbt` | CI Extended の MBT smoke 部分を起動する。 | stateful workflow または trace-transition 変更。 |
| `run-mutation` | mutation auto-diff / scoped mutation を起動する。 | assertion strength または negative-path validation。 |
| `run-property` | CI Extended の property-harness 部分を起動する。 | parser、normalizer、generator、invariant-heavy な変更。 |
| `enforce-coverage` | coverage threshold enforcement を blocking にする。 | report-only baseline を把握した後の coverage-sensitive PR。 |

より広い label 方針は `docs/ci/label-gating.md` を参照してください。

### Coverage baseline と artifact の扱い

- project の coverage command は `pnpm run coverage` です。Vitest reporter により `coverage/coverage-summary.json` と `coverage/lcov.info` を出力します。
- `coverage/` は `.gitignore` で除外されているため、coverage 出力は手動管理する tracked baseline ではなく generated artifact として扱います。
- 文書には運用上の参考として latest observed baseline を記録できますが、現在の baseline は対象 commit でコマンドを再実行して確認します。
- Docker / Podman engine を検出できない host では、non-CI の `pnpm run coverage` が `tests/container/container-agent.test.ts` で失敗する場合があります。CI degraded-mode に合わせた local baseline emulation では `CI=1 pnpm run coverage` を使い、その環境条件を evidence に記録します。

`origin/main` `944fc818dd89a9d51cb72f1c2ee6e1b5cfa3e7e1` で確認した最新 baseline（2026-05-08, `CI=1 pnpm -s run coverage`）:

| Metric | Percent | Covered / Total |
| --- | ---: | ---: |
| Lines | 31.96% | 53,302 / 166,738 |
| Statements | 31.96% | 53,302 / 166,738 |
| Functions | 60.76% | 3,132 / 5,154 |
| Branches | 67.89% | 10,708 / 15,771 |

### docs-only 更新時の検証

planning issue と同じ documentation / type-surface check を実行します。

- `pnpm -s run check:doc-consistency`
- `pnpm -s run check:doc-todo-markers`
- `pnpm -s run check:runbook-command-blocks`
- `pnpm -s run types:check`
