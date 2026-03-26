---
docRole: derived
canonicalSource:
- policy/quality.json
- docs/ci/harness-taxonomy.md
- .github/workflows/adapter-thresholds.yml
lastVerified: '2026-03-27'
---
# Adapter Thresholds — Lighthouse / Perf / A11y

> Language / 言語: English | 日本語

---

## English

Define the adapter-threshold policy for accessibility, performance, and Lighthouse checks. The current repository baseline is report-only by default and becomes blocking only when the relevant enforcement label is added.

- Primary workflow: `.github/workflows/adapter-thresholds.yml`
- Canonical policy context: `policy/quality.json`, `docs/ci/harness-taxonomy.md`
- Output comments:
  - `<!-- AE-ADAPTER-A11Y -->`
  - `<!-- AE-ADAPTER-PERF -->`
  - `<!-- AE-ADAPTER-LH -->`
- Artifacts:
  - `reports/a11y-results.json`
  - `reports/perf-results.json`
  - `reports/lighthouse-results.json`
  - `reports/lh-results.json`

### Baseline policy

- Default behavior is report-only. A PR is not blocked unless the corresponding enforcement label is present.
- Workflow execution itself is gated by the PR label `run-adapters`.
- The workflow does not run for fork PRs because each job requires `github.event.pull_request.head.repo.fork == false`.
- Current enforcement labels:
  - `enforce-a11y`
  - `enforce-perf`
  - `enforce-lh`
- Current threshold override labels:
  - `perf:<score>`
  - `lh:<score>`

### Threshold derivation

#### Accessibility

- `enforce-a11y` switches accessibility from report-only to blocking.
- Threshold is fixed in the workflow:
  - `critical=0`
  - `serious=0`
- The PR comment reports:
  - `Threshold (effective): critical=0, serious=0`
  - `Derived: fixed thresholds (critical=0, serious=0)`
  - `Policy`
  - `Policy source`
  - `Docs`

#### Performance

- `summarize-perf` reads `reports/perf-results.json` when present.
- Accepted score paths are resolved in this order:
  - `.score`
  - `.performance`
  - `.lighthouse.performance`
  - `.metrics.score`
- `enforce-perf` makes the threshold blocking.
- Effective threshold resolution is:
  - `perf:<score>` label
  - `vars.PERF_DEFAULT_THRESHOLD`
  - default `75`
- The PR comment reports `Threshold (effective)` and `Derived: label > repo var > default`.

#### Lighthouse

- `summarize-lh` reads the first existing file from:
  - `reports/lighthouse-results.json`
  - `reports/lh-results.json`
- Accepted score paths are:
  - `.categories.performance.score` (`0..1`, normalized to `0..100`)
  - `.performance`
  - `.score`
- `enforce-lh` makes the threshold blocking.
- Effective threshold resolution is:
  - `lh:<score>` label
  - `vars.LH_DEFAULT_THRESHOLD`
  - default `80`

### Repository variables

Recommended repository variables:

- `PERF_DEFAULT_THRESHOLD`
- `LH_DEFAULT_THRESHOLD`

If these variables are unset, the workflow still runs in report-only mode. When enforcement is enabled, the effective value is still resolved from `label > repo var > default`.

### JSON shape checks

Shape validation is non-blocking and emits `::warning::` messages instead of failing the job.

- a11y:
  - `.violations.critical` and `.violations.serious` must be numeric
  - `.components_tested` is checked as an optional array
- perf:
  - one of `.score`, `.performance`, or `.metrics.score` must be present
- lighthouse:
  - one of `.categories.performance.score`, `.performance`, or `.score` must be present

### Local reproduction

#### A11y

```bash
mkdir -p reports
printf '%s' '{"violations":{"critical":0,"serious":0,"moderate":1,"minor":2},"passes":42,"components_tested":["Button","Link"]}' > reports/a11y-results.json
```

Then add `run-adapters` on the PR so the workflow posts the summary comment. Add `enforce-a11y` only when you want the threshold to block the PR.

#### Perf

```bash
printf '%s' '{"score":87}' > reports/perf-results.json
```

Use `enforce-perf` to block on the effective threshold. Add `perf:<pct>` when an ad hoc override is required.

#### Lighthouse

```bash
printf '%s' '{"categories":{"performance":{"score":0.93}}}' > reports/lighthouse-results.json
```

Use `enforce-lh` to block on the effective threshold. Add `lh:<pct>` when an ad hoc override is required.

### Rollout model

- Phase 1: report-only comments and artifacts
- Phase 2: label-gated enforcement via `enforce-*`
- Phase 3: consider stricter defaults on `main` only after observing stable behavior

### Terminology

- `Derived`: threshold resolution path
- `Policy`: `enforced` or `report-only`
- `Policy source`: why the current policy is enforced or report-only

### Minimal JSON examples

Accessibility (`reports/a11y-results.json`)

```json
{
  "violations": { "critical": 0, "serious": 1, "moderate": 2, "minor": 3 },
  "passes": 120,
  "components_tested": ["Button", "Form"]
}
```

Performance (`reports/perf-results.json`)

```json
{ "score": 78 }
```

Lighthouse (`reports/lighthouse-results.json`)

```json
{ "categories": { "performance": { "score": 0.82 } } }
```

## 日本語

アクセシビリティ、Performance、Lighthouse の adapter threshold 方針を定義する。現行リポジトリでは既定値は report-only で、対応する enforcement label が付いたときだけブロッキングになる。

- 主な workflow: `.github/workflows/adapter-thresholds.yml`
- 正準の方針参照: `policy/quality.json`, `docs/ci/harness-taxonomy.md`
- コメント出力:
  - `<!-- AE-ADAPTER-A11Y -->`
  - `<!-- AE-ADAPTER-PERF -->`
  - `<!-- AE-ADAPTER-LH -->`
- artifact:
  - `reports/a11y-results.json`
  - `reports/perf-results.json`
  - `reports/lighthouse-results.json`
  - `reports/lh-results.json`

### 現行ベースライン

- 既定動作は report-only。対応する enforcement label が無い限り PR はブロックしない。
- workflow 自体の実行条件は PR label `run-adapters`。
- 各 job は `github.event.pull_request.head.repo.fork == false` を要求するため、fork PR では動かない。
- 現在の enforcement label:
  - `enforce-a11y`
  - `enforce-perf`
  - `enforce-lh`
- 現在のしきい値 override label:
  - `perf:<score>`
  - `lh:<score>`

### しきい値の導出

#### Accessibility

- `enforce-a11y` で accessibility を report-only から blocking に切り替える。
- workflow に埋め込まれているしきい値は固定:
  - `critical=0`
  - `serious=0`
- PR コメントには以下が出る:
  - `Threshold (effective): critical=0, serious=0`
  - `Derived: fixed thresholds (critical=0, serious=0)`
  - `Policy`
  - `Policy source`
  - `Docs`

#### Performance

- `summarize-perf` は `reports/perf-results.json` が存在する場合に読む。
- score の解決順は次のとおり:
  - `.score`
  - `.performance`
  - `.lighthouse.performance`
  - `.metrics.score`
- `enforce-perf` でしきい値を blocking にする。
- 実効しきい値の解決順は次のとおり:
  - `perf:<score>` label
  - `vars.PERF_DEFAULT_THRESHOLD`
  - 既定値 `75`
- PR コメントには `Threshold (effective)` と `Derived: label > repo var > default` が出る。

#### Lighthouse

- `summarize-lh` は次のうち最初に存在したファイルを読む:
  - `reports/lighthouse-results.json`
  - `reports/lh-results.json`
- score の解決対象は次のとおり:
  - `.categories.performance.score`（`0..1` を `0..100` に正規化）
  - `.performance`
  - `.score`
- `enforce-lh` でしきい値を blocking にする。
- 実効しきい値の解決順は次のとおり:
  - `lh:<score>` label
  - `vars.LH_DEFAULT_THRESHOLD`
  - 既定値 `80`

### Repository Variables

推奨する repository variable:

- `PERF_DEFAULT_THRESHOLD`
- `LH_DEFAULT_THRESHOLD`

これらが未設定でも workflow は report-only で動作する。enforcement を有効化した場合でも、実効値の解決順は `label > repo var > default` のまま。

### JSON shape check

shape 検証は non-blocking で、job を fail させず `::warning::` を出力する。

- a11y:
  - `.violations.critical` と `.violations.serious` が数値であること
  - `.components_tested` は任意の配列として確認
- perf:
  - `.score` / `.performance` / `.metrics.score` のいずれかが存在すること
- lighthouse:
  - `.categories.performance.score` / `.performance` / `.score` のいずれかが存在すること

### ローカル再現

#### A11y

```bash
mkdir -p reports
printf '%s' '{"violations":{"critical":0,"serious":0,"moderate":1,"minor":2},"passes":42,"components_tested":["Button","Link"]}' > reports/a11y-results.json
```

その後、PR に `run-adapters` を付けて workflow の要約コメントを確認する。しきい値を block させたい場合だけ `enforce-a11y` を併用する。

#### Perf

```bash
printf '%s' '{"score":87}' > reports/perf-results.json
```

実効しきい値で block したい場合は `enforce-perf` を付ける。ad hoc override が必要な場合は `perf:<pct>` を追加する。

#### Lighthouse

```bash
printf '%s' '{"categories":{"performance":{"score":0.93}}}' > reports/lighthouse-results.json
```

実効しきい値で block したい場合は `enforce-lh` を付ける。ad hoc override が必要な場合は `lh:<pct>` を追加する。

### 段階導入

- Phase 1: report-only のコメントと artifact
- Phase 2: `enforce-*` による label-gated enforcement
- Phase 3: 安定運用を観測した後に `main` の既定値を厳格化するか検討

### 用語

- `Derived`: しきい値の導出経路
- `Policy`: `enforced` または `report-only`
- `Policy source`: なぜその policy になっているか

### 最小 JSON 例

Accessibility (`reports/a11y-results.json`)

```json
{
  "violations": { "critical": 0, "serious": 1, "moderate": 2, "minor": 3 },
  "passes": 120,
  "components_tested": ["Button", "Form"]
}
```

Performance (`reports/perf-results.json`)

```json
{ "score": 78 }
```

Lighthouse (`reports/lighthouse-results.json`)

```json
{ "categories": { "performance": { "score": 0.82 } } }
```
