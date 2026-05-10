---
docRole: derived
canonicalSource:
- docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md
- docs/product/ASSURANCE-CONTROL-PLANE.md
- docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md
- docs/reference/CONTRACT-CATALOG.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-05-09'
---
# Assurance Canonical Routes and Legacy Compatibility

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This reference document resolves the duplicate route findings from the assurance control-plane current-state report. It does not remove commands, schemas, workflows, or artifacts. It marks the preferred route for new documentation and PR/release evidence, while preserving compatibility routes that still have consumers.

### 2. Canonical route matrix

| Area | Canonical route for new work | Compatibility or preview route | Operator note |
| --- | --- | --- | --- |
| Product and policy positioning | `docs/product/ASSURANCE-CONTROL-PLANE.md`, `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` | Older product overviews that mention verification or agents indirectly | Link to the product/policy docs before adding another assurance-control-plane overview. |
| Detailed assurance design | `docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md` | Distributed explanations in quality, CI, integration, and reference docs | Use the detailed design for claim/evidence/waiver/policy/change-package semantics. |
| Contract inventory | `docs/reference/CONTRACT-CATALOG.md` | Individual schema README-style notes | Use the catalog to identify producer and consumer boundaries before changing a schema. |
| Quality scorecard | `quality-scorecard/v1`: `schema/quality-scorecard.schema.json`, `scripts/quality/build-quality-scorecard.mjs`, `pnpm run quality:scorecard:v1`, `pnpm run quality:scorecard:validate` | Legacy `pnpm run quality:scorecard` / `scripts/quality-scorecard-generator.js` | New PR/release evidence should use v1. The legacy command remains a compatibility diagnostic route unless callers supply both `--verify-lite-summary` and `--report-envelope`; `--legacy` and `--legacy-diagnostic` force the legacy diagnostic path. |
| Formal evidence status | `artifacts/formal/formal-summary-v2.json` plus `artifacts/formal/formal-summary-v1.json` during dual-write; aggregate view: `artifacts/hermetic-reports/formal/summary.json` | Legacy `formal/summary.json` | Treat `formal/summary.json` as a final compatibility input only. PR summary rendering now reads formal-summary v2/v1 and the hermetic aggregate before the legacy fallback; new producers should emit the formal summary v1/v2 artifacts or the hermetic aggregate. |
| Counterexample GWT summary | `artifacts/formal/gwt.summary.json` produced by `scripts/formal/format-counterexamples.mjs` | Embedded counterexamples in legacy `formal/summary.json` | The GWT summary is a derived aid for humans and `ae fix`; it is not the primary formal status contract. |
| PR summary judgment surface | `scripts/summary/render-pr-summary.mjs` plus `.github/workflows/pr-ci-status-comment.yml` append stage | Hand-authored PR summaries or older one-off bot comments | Keep renderer direct inputs separate from workflow-appended Markdown artifacts. |
| Policy gate judgment | `.github/workflows/policy-gate.yml`, `scripts/ci/policy-gate.mjs`, `policy/risk-policy.rego`, `schema/policy-*.schema.json` | Shadow compare output without a dedicated schema | Assurance sections stay report-only unless an explicit enforcement mode is selected. |
| Claim-level judgment | `claim-level-summary/v1`: `schema/claim-level-summary-v1.schema.json`, `pnpm run claim-level-summary:generate` | Claim-evidence manifest `achievedLevel` fields alone | Use the summary when a PR/release needs one compact per-claim view. |
| Change package | Production: `change-package/v1`; proof-carrying preview: `change-package/v2` via dual-write/dual-validate commands | Directly reading source artifact fragments | Keep v1 compatibility while using v2 for proof-carrying previews and E2E validation. |
| Spec & Verification Kit | `docs/reference/SPEC-VERIFICATION-KIT-MIN.md` plus `docs/reference/SPEC-VERIFICATION-KIT-EXTENSIONS.md` | Tool-specific runbooks without the kit activation context | Use the kit docs to choose which evidence producers are in scope for an assurance run. |
| Agent runbooks | `docs/integrations/ASSURANCE-AGENT-RUNBOOK.md` | Standalone Codex, Claude, or MCP guides | Treat agents as replaceable evidence producers, not as the assurance-control-plane boundary. |
| Current-state validation | `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md` and `docs/reports/ASSURANCE-CONTROL-PLANE-E2E-VALIDATION.md` | Ad hoc local notes | Use these reports to justify cleanup and coverage claims. |

### 3. Compatibility rules

- Preserve a legacy command or artifact path while a workflow, renderer, release script, or documented operator flow still reads it.
- Mark compatibility routes with their replacement link before removing or repointing them.
- Back workflow or script cleanup with tests that cover the affected consumer path.
- Prefer report-only documentation when the replacement is not yet enforced by CI.
- Keep README and index pages pointed at the canonical route first, with compatibility notes secondary.

### 4. Cleanup backlog that still needs tests

| Candidate cleanup | Current blocker | Minimum evidence before changing behavior |
| --- | --- | --- |
| Repoint `quality:scorecard` to v1 | The compatibility script now delegates to v1 when required inputs are supplied, but no-input legacy diagnostic callers can still exist. | Keep the wrapper test and migrate workflow/operator callers to supply `verify-lite-run-summary` and `report-envelope` before removing no-input legacy behavior. |
| Keep `formal/summary.json` as final PR summary compatibility fallback | `render-pr-summary.mjs` and the workflow inline fallback now read formal-summary v2/v1 and the hermetic aggregate before `formal/summary.json`. Full removal still needs consumer migration evidence. | Maintain renderer/workflow tests that prove canonical artifacts populate the formal line and legacy fallback still works until all consumers are migrated. |
| Make `format-counterexamples.mjs` independent of legacy `formal/summary.json` | The current script reads the legacy path as the source counterexample container. | Unit tests and fixture updates that derive `artifacts/formal/gwt.summary.json` from a current formal summary or aggregate source. |
| Remove duplicate judgment explanations from older docs | Older docs still carry useful operator context. | Index updates and redirects/replacement links that preserve discoverability. |

---

## 日本語

### 1. 目的

この参照ドキュメントは、assurance control-plane current-state report で見つかった重複導線を整理します。コマンド、スキーマ、workflow、artifact は削除しません。新しいドキュメントや PR / release evidence で優先する導線を明示し、既存 consumer が残る互換導線は残します。

### 2. 正準導線マトリクス

| 領域 | 新規作業で優先する正準導線 | 互換または preview 導線 | 運用メモ |
| --- | --- | --- | --- |
| Product / policy 位置付け | `docs/product/ASSURANCE-CONTROL-PLANE.md`, `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` | verification や agent を間接的に扱う古い product overview | 新しい overview を追加する前に product / policy docs へリンクする。 |
| 詳細設計 | `docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md` | quality / CI / integration / reference docs に分散した説明 | claim / evidence / waiver / policy / change-package semantics は詳細設計を優先する。 |
| Contract inventory | `docs/reference/CONTRACT-CATALOG.md` | 個別 schema の README 的な注記 | schema 変更前に producer / consumer 境界を catalog で確認する。 |
| Quality scorecard | `quality-scorecard/v1`: `schema/quality-scorecard.schema.json`, `scripts/quality/build-quality-scorecard.mjs`, `pnpm run quality:scorecard:v1`, `pnpm run quality:scorecard:validate` | legacy `pnpm run quality:scorecard` / `scripts/quality-scorecard-generator.js` | 新しい PR / release evidence は v1 を使う。legacy command は入力なしでは互換 diagnostic route を維持し、`--verify-lite-summary` と `--report-envelope` が渡された場合は v1 に委譲する。 |
| Formal evidence status | `artifacts/formal/formal-summary-v2.json` と dual-write 期間の `artifacts/formal/formal-summary-v1.json`; aggregate view は `artifacts/hermetic-reports/formal/summary.json` | legacy `formal/summary.json` | `formal/summary.json` は final compatibility input としてのみ扱う。PR summary rendering は formal-summary v2/v1 と hermetic aggregate を legacy fallback より先に読む。新規 producer は formal summary v1/v2 または hermetic aggregate を出す。 |
| Counterexample GWT summary | `scripts/formal/format-counterexamples.mjs` が生成する `artifacts/formal/gwt.summary.json` | legacy `formal/summary.json` に埋め込まれた counterexample | GWT summary は人間と `ae fix` 向けの派生成果物であり、primary formal status contract ではない。 |
| PR summary judgment surface | `scripts/summary/render-pr-summary.mjs` と `.github/workflows/pr-ci-status-comment.yml` append stage | 手書き PR summary や古い単発 bot comment | renderer の direct input と workflow が追記する Markdown artifact を分ける。 |
| Policy gate judgment | `.github/workflows/policy-gate.yml`, `scripts/ci/policy-gate.mjs`, `policy/risk-policy.rego`, `schema/policy-*.schema.json` | 専用 schema 未整備の shadow compare output | 明示的な enforcement mode を選ばない限り、assurance section は report-only として扱う。 |
| Claim-level judgment | `claim-level-summary/v1`: `schema/claim-level-summary-v1.schema.json`, `pnpm run claim-level-summary:generate` | claim-evidence manifest の `achievedLevel` field 単体 | PR / release で claim 単位の compact view が必要な場合は summary を使う。 |
| Change package | production は `change-package/v1`; proof-carrying preview は dual-write / dual-validate command 経由の `change-package/v2` | source artifact fragment の直接参照 | v1 互換を維持しつつ、proof-carrying preview と E2E validation には v2 を使う。 |
| Spec & Verification Kit | `docs/reference/SPEC-VERIFICATION-KIT-MIN.md` と `docs/reference/SPEC-VERIFICATION-KIT-EXTENSIONS.md` | kit activation context を持たない tool 固有 runbook | assurance run の対象 producer を選ぶ際は kit docs を使う。 |
| Agent runbooks | `docs/integrations/ASSURANCE-AGENT-RUNBOOK.md` | Codex / Claude / MCP の個別 guide | agent は置換可能な evidence producer として扱い、assurance-control-plane boundary とはしない。 |
| Current-state validation | `docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md` と `docs/reports/ASSURANCE-CONTROL-PLANE-E2E-VALIDATION.md` | ad hoc local notes | cleanup や coverage claim の根拠にはこれらの report を使う。 |

### 3. 互換ルール

- workflow、renderer、release script、文書化された operator flow が読む間は、legacy command または artifact path を維持する。
- 互換導線を削除または差し替える前に、replacement link を明示する。
- workflow / script cleanup は、影響する consumer path を覆う test と一緒に実施する。
- replacement が CI enforcement されていない場合は、report-only として文書化する。
- README と index は、正準導線を先に示し、互換注記は secondary として扱う。

### 4. test が必要な残 cleanup

| cleanup 候補 | 現在の blocker | 挙動変更前に必要な最低証跡 |
| --- | --- | --- |
| `quality:scorecard` を v1 に向ける | 互換 script は必須入力が渡された場合に v1 へ委譲するが、入力なし legacy diagnostic caller は残り得る。 | wrapper test を維持し、入力なし legacy 挙動を削除する前に workflow / operator caller が `verify-lite-run-summary` と `report-envelope` を渡すよう移行する。 |
| `formal/summary.json` を PR summary の final compatibility fallback として維持する | `render-pr-summary.mjs` と workflow inline fallback は formal-summary v2/v1 と hermetic aggregate を `formal/summary.json` より先に読む。完全削除には consumer migration evidence がまだ必要。 | current canonical artifact から formal line が埋まり、legacy fallback も残ることを示す renderer / workflow tests を維持する。 |
| `format-counterexamples.mjs` を legacy `formal/summary.json` から独立させる | 現行 script は legacy path を counterexample container として読む。 | current formal summary または aggregate source から `artifacts/formal/gwt.summary.json` を生成する unit test と fixture 更新。 |
| 古い docs の重複 judgment 説明を削減する | 古い docs にも有用な operator context が残っている。 | discoverability を維持する index 更新と replacement link。 |
