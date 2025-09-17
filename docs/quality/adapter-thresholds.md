# Adapter Thresholds — Lighthouse/Perf/A11y (Label-Gated)

Purpose（決定）
- Adapter thresholds は「PRは非ブロッキング、必要時ラベルで強制」の方針とする（段階導入）。

Proposal
- PRは非ブロッキング（report-only）。必要に応じてラベルで強制・しきい値上書きを行う。
- Example labels (to be wired incrementally):
  - `enforce-a11y`, `enforce-perf`, `enforce-lh` — turn results into gates
  - `a11y:<score>`, `perf:<score>` — override thresholds ad hoc

Repository variables（推奨/決定）
- `PERF_DEFAULT_THRESHOLD`（未設定時は既定 75）
- `LH_DEFAULT_THRESHOLD`（未設定時は既定 80）
未設定の場合でもレポートは非ブロッキングで動作します（強制時はラベル/値の解決順：ラベル > 変数 > 既定）。

Current wiring (a11y minimal)
- `run-adapters`: runs adapter-thresholds.yml to summarize `reports/a11y-results.json` on PR (non-blocking)
- `enforce-a11y`: enforces minimal thresholds (critical=0, serious=0). Job fails if violated.
- PR comment fields: Threshold (effective) / Derived（固定: critical=0, serious=0）/ Policy / Docs

Perf (proposal → minimal wiring)
- `reports/perf-results.json` が存在する場合にスコアを要約（非ブロッキング）
- `enforce-perf` ラベルでしきい値を強制（`perf:<score>` ラベルで上書き。既定は `vars.PERF_DEFAULT_THRESHOLD` または 75）
- PRコメント: Threshold (effective) / Derived（label > repo var > default）/ Policy / Policy source / Docs
- Slash Commands: `/enforce-perf`, `/perf <pct|clear>`

Lighthouse (proposal → minimal wiring)
- `reports/lighthouse-results.json`（または `reports/lh-results.json`）から performance スコアを要約（非ブロッキング）
- `enforce-lh` ラベルでしきい値を強制（`lh:<score>` ラベルで上書き。既定は `vars.LH_DEFAULT_THRESHOLD` または 80）
- PRコメント: Threshold (effective) / Derived（label > repo var > default）/ Policy / Policy source / Docs
- Slash Commands: `/enforce-lh`, `/lh <pct|clear>`

Phasing（段階導入）
- Phase 1: Reporting only（PRコメント/アーティファクト）
- Phase 2: Label-gated enforcement（`enforce-*` ラベルでブロック化）
- Phase 3: main 既定（観測後に検討）

Notes
- See `quality-gates-centralized.yml` for central jobs and consider adding thresholds as follow-up.
 - File: `.github/workflows/adapter-thresholds.yml`

JSON shape checks（非ブロッキング警告）
- a11y: `.violations.critical` / `.violations.serious` が数値、`.components_tested` が配列かを軽く検証
- perf: `.score` or `.performance`（0..100）、もしくは `.metrics.score`
- lighthouse: `.categories.performance.score`（0..1） or `.performance`（0..100） or `.score`
形状が想定外の場合は `::warning::` を出力（ジョブは継続）

CLI (quick local reproduction)
- a11y (report-only JSONを用意してPRでのコメント確認)
  - `mkdir -p reports && printf '%s' '{"violations":{"critical":0,"serious":0,"moderate":1,"minor":2},"passes":42,"components_tested":["Button","Link"]}' > reports/a11y-results.json`
  - PRに `/run-adapters` を付与 → Verify Lite or CI Fast 実行（コメントに要約が表示）
- perf / lighthouse（scoreの最小JSON例）
  - perf: `printf '%s' '{"score":87}' > reports/perf-results.json`
- lighthouse: `printf '%s' '{"categories":{"performance":{"score":0.93}}}' > reports/lighthouse-results.json`
- 必要に応じ `/enforce-perf` や `/perf <pct>`、`/enforce-lh` や `/lh <pct>` を併用

Enforcement notes
- 既定は report-only（PR をブロックしません）。`/enforce-perf` や `/enforce-lh` を付与するとブロッキング化します。
- しきい値の導出順は「ラベル（perf:<pct>/lh:<pct>）> リポジトリ変数（PERF_DEFAULT_THRESHOLD/LH_DEFAULT_THRESHOLD）> 既定（perf=75, lh=80）」です。
- 変数未設定でも動作しますが、しきい値の既定を統一するためリポジトリ変数を設定する運用を推奨します。

Glossary（表示用語の統一）
- Derived: `label > repo var > default`（しきい値の導出順）
- Policy: `enforced | report-only`
- Policy source: `enforced via label: enforce-<name>` or `report-only`

### Minimal JSON examples

Accessibility (reports/a11y-results.json)
```
{
  "violations": { "critical": 0, "serious": 1, "moderate": 2, "minor": 3 },
  "passes": 120,
  "components_tested": ["Button", "Form"]
}
```

Performance (reports/perf-results.json)
```
{ "score": 78 }
```

Lighthouse (reports/lighthouse-results.json)
```
{ "categories": { "performance": { "score": 0.82 } } }
```
