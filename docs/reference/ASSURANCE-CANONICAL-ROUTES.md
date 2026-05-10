---
docRole: derived
canonicalSource:
- docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md
- docs/product/ASSURANCE-CONTROL-PLANE.md
- docs/architecture/ASSURANCE-CONTROL-PLANE-DETAILED-DESIGN.md
- docs/reference/CONTRACT-CATALOG.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-05-10'
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
| Counterexample GWT summary | `artifacts/formal/gwt.summary.json` produced by `scripts/formal/format-counterexamples.mjs` from canonical aggregate/tool evidence that embeds counterexamples, especially `artifacts/hermetic-reports/formal/summary.json` and `artifacts/formal/formal-aggregate.json` | Embedded counterexamples in legacy `formal/summary.json` | The GWT summary is a derived aid for humans and `ae fix`; it is not the primary formal status contract. The formatter reads aggregate/tool sources before the legacy fallback. |
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

### 4. Cleanup backlog and disposition

Every legacy or compatibility route listed in this document currently has an explicit disposition. These dispositions are intentionally conservative: compatibility behavior stays available until consumer-path tests and rollback notes prove that a behavior change is safe.

| Candidate cleanup | Disposition | Current blocker | Minimum evidence before changing behavior | Rollback guidance |
| --- | --- | --- | --- | --- |
| Repoint `quality:scorecard` to v1 | `legacy-compatible` / keep wrapper | The compatibility script now delegates to v1 when required inputs are supplied, but no-input legacy diagnostic callers can still exist. | Keep the wrapper test and migrate workflow/operator callers to supply `verify-lite-run-summary` and `report-envelope` before removing no-input legacy behavior. | Restore the wrapper branch to call `scripts/quality-scorecard-generator.js` for affected callers and keep `quality:scorecard:v1` available as the canonical route. |
| Keep `formal/summary.json` as final PR summary compatibility fallback | `legacy-compatible` / canonical aggregate preferred | `render-pr-summary.mjs` and the workflow inline fallback now read formal-summary v2/v1 and the hermetic aggregate before `formal/summary.json`. Full removal still needs consumer migration evidence. | Maintain renderer/workflow tests that prove canonical artifacts populate the formal line and legacy fallback still works until all consumers are migrated. | Re-enable the legacy fallback read path and document the consumer that still requires it. |
| Keep `format-counterexamples.mjs` independent of legacy `formal/summary.json` | `legacy-compatible` / canonical aggregate preferred | The script now reads the hermetic aggregate and `artifacts/formal/formal-aggregate.json` before the legacy compatibility fallback. Full removal of the fallback still needs consumer migration evidence. | Maintain formatter tests that derive `artifacts/formal/gwt.summary.json` from a current formal aggregate source and verify legacy fallback remains available. | Restore the legacy fallback parser while keeping canonical aggregate parsing first. |
| Remove duplicate judgment explanations from older docs | `legacy-compatible` / docs-only cleanup | Older docs still carry useful operator context. | Index updates and redirects/replacement links that preserve discoverability. | Revert the docs-only consolidation and keep replacement links in the canonical route map. |

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
| Counterexample GWT summary | `scripts/formal/format-counterexamples.mjs` が counterexample を埋め込む canonical aggregate / tool evidence、特に `artifacts/hermetic-reports/formal/summary.json` と `artifacts/formal/formal-aggregate.json` から生成する `artifacts/formal/gwt.summary.json` | legacy `formal/summary.json` に埋め込まれた counterexample | GWT summary は人間と `ae fix` 向けの派生成果物であり、primary formal status contract ではない。formatter は legacy fallback より先に aggregate / tool source を読む。 |
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

### 4. cleanup backlog と disposition

本ドキュメントに列挙した legacy / compatibility route は、現時点で明示的な disposition を持ちます。挙動変更は保守的に扱い、consumer-path test と rollback note が揃うまで互換挙動を維持します。

| cleanup 候補 | disposition | 現在の blocker | 挙動変更前に必要な最低証跡 | rollback guidance |
| --- | --- | --- | --- | --- |
| `quality:scorecard` を v1 に向ける | `legacy-compatible` / wrapper 維持 | 互換 script は必須入力が渡された場合に v1 へ委譲するが、入力なし legacy diagnostic caller は残り得る。 | wrapper test を維持し、入力なし legacy 挙動を削除する前に workflow / operator caller が `verify-lite-run-summary` と `report-envelope` を渡すよう移行する。 | 影響 caller 向けに wrapper branch を `scripts/quality-scorecard-generator.js` 呼び出しへ戻し、canonical route として `quality:scorecard:v1` は維持する。 |
| `formal/summary.json` を PR summary の final compatibility fallback として維持する | `legacy-compatible` / canonical aggregate 優先 | `render-pr-summary.mjs` と workflow inline fallback は formal-summary v2/v1 と hermetic aggregate を `formal/summary.json` より先に読む。完全削除には consumer migration evidence がまだ必要。 | current canonical artifact から formal line が埋まり、legacy fallback も残ることを示す renderer / workflow tests を維持する。 | legacy fallback read path を戻し、まだ必要としている consumer を文書化する。 |
| `format-counterexamples.mjs` を legacy `formal/summary.json` から独立した状態で維持する | `legacy-compatible` / canonical aggregate 優先 | script は hermetic aggregate と `artifacts/formal/formal-aggregate.json` を legacy compatibility fallback より先に読む。fallback の完全削除には consumer migration evidence がまだ必要。 | current formal aggregate source から `artifacts/formal/gwt.summary.json` を生成し、legacy fallback も残ることを示す formatter test を維持する。 | canonical aggregate parsing を優先したまま、legacy fallback parser を戻す。 |
| 古い docs の重複 judgment 説明を削減する | `legacy-compatible` / docs-only cleanup | 古い docs にも有用な operator context が残っている。 | discoverability を維持する index 更新と replacement link。 | docs-only consolidation を revert し、canonical route map には replacement link を残す。 |
