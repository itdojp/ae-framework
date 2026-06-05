---
docRole: derived
canonicalSource:
- docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
- docs/product/ASSURANCE-CONTROL-PLANE.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-06-05'
---

# Agent Producer Matrix

> Language / 言語: English | 日本語

---

## English

This matrix defines how producer output enters the ae-framework assurance control plane. Producers can generate code, review comments, raw logs, test results, or tool responses. ae-framework does not treat those outputs as trusted by default; it normalizes them into contract-backed artifacts that reviewers, policy gates, and release decisions can inspect.

Use this document with:

- `docs/spec/context-pack.md` and `spec/context-pack/boundary-map.json` for the design SSOT and implementation slice boundaries that producers must read before changing code.
- `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` for the producer/control-plane boundary.
- `docs/reference/CONTRACT-CATALOG.md` for schema-backed artifact names.
- `docs/agents/evidence-adapters.md` for raw producer output fixture mapping.
- `docs/integrations/CODEX-ISSUE-RUNBOOK.md` for the Codex CLI issue workflow.
- `docs/agents/handoff.md` and `docs/agents/hook-feedback.md` for agent continuation artifacts.

### Producer-to-artifact matrix

| Producer | Example entrypoint | Primary output | Trust boundary | Normalized ae-framework artifact | Required validation | Failure / waiver handling |
| --- | --- | --- | --- | --- | --- | --- |
| Codex CLI local task | `codex exec --cd <repo> ...` or interactive `codex --cd <repo>` | local diff, command output, task summary | local workspace and tool permissions are producer-side; generated changes are untrusted until reviewed | `change-package/v2`, `ae-handoff/v1`, `hook-feedback/v1`, `claim-evidence-manifest/v1` when claims/evidence are present | `git diff --stat`, relevant tests, `pnpm -s run check:doc-consistency`, `pnpm -s run check:schemas`, PR checks | record missing commands in the PR; unresolved claims stay `unresolved`; waivers require owner, reason, expiry, and claim link |
| Codex cloud / GitHub Action task | workflow job, `issue_comment`, or scheduled automation | PR branch, generated artifact logs, automation comments | GitHub Actions token and workflow permissions are separate from review authority | `policy-decision/v1`, `hook-feedback/v1`, `verify-lite-run-summary`, `quality-scorecard`, optional `change-package/v2` | required checks `verify-lite`, `policy-gate`, `gate`; artifact validation; review thread completeness | failed checks become blocking reasons; stale or superseded checks must be explained; waivers do not convert missing evidence into supported evidence |
| Claude Code task | `CLAUDE.md` routed task or Claude Code automation | diff, tool log, task response, handoff notes | Claude Code is a producer; repository policy remains in ae-framework contracts | `ae-handoff/v1`, `hook-feedback/v1`, `change-package/v2`, `claim-evidence-manifest/v1` | run the same repo validation commands as a human maintainer; validate handoff JSON when generated | keep continuation blockers explicit; unsupported claims remain `unresolved`; manual exceptions require waiver metadata |
| GitHub Copilot cloud agent PR | Copilot-created or Copilot-reviewed PR | PR diff, review body, inline comments, suggestions | Copilot comments are review input, not control-plane evidence until addressed and resolved | `policy-decision/v1`, PR summary, optional `change-package/v2`; review thread state stays source evidence | `pr-review-completeness`, required checks, policy labels, changed-file review | unresolved AI review threads block gate; non-actionable comments need a reply explaining disposition |
| Human maintainer | local commit, PR review, merge decision | diff, approval, manual judgment, waiver decision | human approval can override policy only when recorded with traceable metadata | `change-package/v2`, `policy-decision/v1`, waiver entries in claim/change artifacts, PR review records | branch protection, required checks, reviewer policy, waiver completeness | waivers require owner, reason, expiry, affected claim, and evidence link; unresolved risk remains visible in summaries |
| Test runner / CI job | `pnpm run test:fast`, `verify-lite`, GitHub Actions job | pass/fail, coverage, JUnit/log artifacts, step summaries | raw logs are producer output; summaries are review input after schema/path validation | `verify-lite-run-summary`, `report-envelope`, `quality-scorecard`, `hook-feedback/v1` | schema validation, required-check status, reproducible command path | failing steps become blockers or warnings according to risk/profile; flaky or unavailable tests require explicit reason and follow-up |
| Formal runner / model checker / proof tool | `pnpm run verify:formal`, `verify:tla`, `verify:csp`, `verify:lean` | proof/model-check result, counterexample, assumptions | tool output supports only the modeled/proved scope; it is not whole-product proof | `formal-summary/v2` (dual-write `formal-summary/v1` only for compatibility), `assurance-summary/v1`, `claim-evidence-manifest/v1`, optional `change-package/v2` | formal summary v2/v1 generation and schema validation, assumption and scope review | counterexamples remain blocking evidence for affected claims; bounded/model assumptions must be recorded; waiver cannot relabel failed proof as `proved` |
| MCP tool server | `pnpm run codex:mcp:*` or configured MCP stdio server | tool response JSON, generated spec/test/code snippets | MCP tool response is producer output; caller permissions and path policy stay outside trust | `TaskResponse`, `ae-handoff/v1`, `hook-feedback/v1`, downstream `change-package/v2` when changes are made | TaskResponse schema, path/approval policy, relevant generated-artifact validation | invalid tool output is rejected; missing next actions or blocked responses must remain explicit |

### Operating rules

1. Producer outputs are inputs to judgment, not judgment themselves.
2. Context Pack and Boundary Map are pre-change design inputs, not producer outputs; if a producer diff conflicts with them, stop and resolve the design conflict first.
3. Summary artifacts are the primary review surface; raw logs are supporting evidence.
4. Code generation, agent review, formal proof, and CI execution are separate producer lanes and must not be conflated.
5. `proved`, `model-checked`, `tested`, `runtime-mitigated`, `waived`, and `unresolved` remain distinct claim states.
6. New producers should start report-only unless a policy, label, or risk profile explicitly selects enforcement.

### Artifact routing quick reference

| Need | Prefer this artifact | Notes |
| --- | --- | --- |
| Explain what changed and why it is reviewable | `change-package/v2` | Connects diff scope, claims, evidence, waivers, and policy decisions. |
| Normalize raw Codex / Claude Code / Copilot / human output | `docs/agents/evidence-adapters.md` fixture mapping, then existing artifacts | Fixtures are examples, not contracts; use existing generators and validators. |
| Hand work from one agent/session to another | `ae-handoff/v1` | Use with `docs/agents/handoff.md`. |
| Return compact blockers and next actions to a producer | `hook-feedback/v1` | Use with `docs/agents/hook-feedback.md`. |
| Link claims to supporting evidence | `claim-evidence-manifest/v1` | Claim states must match the evidence lane. |
| Capture policy gate judgment | `policy-decision/v1` | Policy decision is a judgment artifact, not a raw log. |
| Summarize fast-lane PR health | `verify-lite-run-summary` and `quality-scorecard` | These are review inputs for required checks and PR comments. |

---

## 日本語

この matrix は、producer output を ae-framework の assurance control plane へ接続するための境界を定義します。Producer は code、review comment、raw log、test result、tool response を生成できます。ただし ae-framework はそれらをそのまま信頼せず、review / policy gate / release 判断で使える contract-backed artifact へ正規化します。

併読資料:

- `docs/spec/context-pack.md` と `spec/context-pack/boundary-map.json`: producer がコード変更前に読む design SSOT と実装slice境界。
- `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md`: producer と control plane の境界。
- `docs/reference/CONTRACT-CATALOG.md`: schema-backed artifact 名。
- `docs/agents/evidence-adapters.md`: raw producer output の fixture mapping。
- `docs/integrations/CODEX-ISSUE-RUNBOOK.md`: Codex CLI の Issue 作業導線。
- `docs/agents/handoff.md` / `docs/agents/hook-feedback.md`: agent 継続用 artifact。

### Producer-to-artifact matrix

| Producer | Example entrypoint | Primary output | Trust boundary | Normalized ae-framework artifact | Required validation | Failure / waiver handling |
| --- | --- | --- | --- | --- | --- | --- |
| Codex CLI local task | `codex exec --cd <repo> ...` または `codex --cd <repo>` | local diff、command output、task summary | local workspace と tool 権限は producer 側。生成差分は review まで未信頼 | `change-package/v2`, `ae-handoff/v1`, `hook-feedback/v1`, claim/evidence がある場合は `claim-evidence-manifest/v1` | `git diff --stat`、関連 test、`pnpm -s run check:doc-consistency`、`pnpm -s run check:schemas`、PR checks | 未実行 command は PR に記録。証跡不足の claim は `unresolved`。waiver には owner / reason / expiry / claim link が必要 |
| Codex cloud / GitHub Action task | workflow job、`issue_comment`、scheduled automation | PR branch、artifact log、automation comment | GitHub Actions token / workflow 権限は review authority と別 | `policy-decision/v1`, `hook-feedback/v1`, `verify-lite-run-summary`, `quality-scorecard`, optional `change-package/v2` | required checks `verify-lite`, `policy-gate`, `gate`、artifact validation、review thread completeness | failed check は blocking reason。stale / superseded check は説明する。waiver は missing evidence を supported に変換しない |
| Claude Code task | `CLAUDE.md` routed task または Claude Code automation | diff、tool log、task response、handoff note | Claude Code は producer。repository policy は ae-framework contract 側に残す | `ae-handoff/v1`, `hook-feedback/v1`, `change-package/v2`, `claim-evidence-manifest/v1` | human maintainer と同じ repo validation。handoff JSON を生成した場合は検証 | continuation blocker を明示。unsupported claim は `unresolved`。例外は waiver metadata が必要 |
| GitHub Copilot cloud agent PR | Copilot-created / Copilot-reviewed PR | PR diff、review body、inline comment、suggestion | Copilot comment は review input。対応・解決まで control-plane evidence ではない | `policy-decision/v1`、PR summary、optional `change-package/v2`。review thread state は source evidence に留める | `pr-review-completeness`、required checks、policy labels、changed-file review | unresolved AI review thread は gate を block。対応不要コメントには disposition を返信する |
| Human maintainer | local commit、PR review、merge decision | diff、approval、manual judgment、waiver decision | human approval は traceable metadata がある場合だけ policy override になる | `change-package/v2`, `policy-decision/v1`, claim/change artifact の waiver entry、PR review record | branch protection、required checks、reviewer policy、waiver completeness | waiver は owner / reason / expiry / affected claim / evidence link を持つ。unresolved risk は summary に残す |
| Test runner / CI job | `pnpm run test:fast`, `verify-lite`, GitHub Actions job | pass/fail、coverage、JUnit/log artifact、step summary | raw log は producer output。summary は schema/path validation 後に review input になる | `verify-lite-run-summary`, `report-envelope`, `quality-scorecard`, `hook-feedback/v1` | schema validation、required-check status、reproducible command path | failed step は risk/profile に応じて blocker または warning。flake / unavailable test は理由と follow-up を明示 |
| Formal runner / model checker / proof tool | `pnpm run verify:formal`, `verify:tla`, `verify:csp`, `verify:lean` | proof/model-check result、counterexample、assumption | tool output は model/proof scope のみを支える。製品全体の証明ではない | `formal-summary/v2`（`formal-summary/v1` は compatibility dual-write のみ）, `assurance-summary/v1`, `claim-evidence-manifest/v1`, optional `change-package/v2` | formal summary v2/v1 generation と schema validation、assumption/scope review | counterexample は affected claim の blocking evidence。bounded/model assumption を記録。waiver は failed proof を `proved` にしない |
| MCP tool server | `pnpm run codex:mcp:*` または MCP stdio server | tool response JSON、generated spec/test/code snippet | MCP response は producer output。caller permission と path policy は trust boundary の外側 | `TaskResponse`, `ae-handoff/v1`, `hook-feedback/v1`, 変更時は downstream `change-package/v2` | TaskResponse schema、path/approval policy、関連 generated-artifact validation | invalid tool output は rejected。missing next action / blocked response は明示したままにする |

### 運用ルール

1. Producer output は判断の入力であり、判断そのものではありません。
2. Context Pack と Boundary Map は producer output ではなく、変更前に参照するdesign inputです。producer差分がこれらと衝突する場合は、先に設計衝突を解決します。
3. Summary artifact を review の一次情報とし、raw log は補助証跡に留めます。
4. Code generation、agent review、formal proof、CI execution は別々の producer lane であり、混同しません。
5. `proved`、`model-checked`、`tested`、`runtime-mitigated`、`waived`、`unresolved` は別状態として扱います。
6. 新しい producer は、policy / label / risk profile が enforcement を選ぶまで report-only から始めます。

### Artifact routing quick reference

| Need | Prefer this artifact | Notes |
| --- | --- | --- |
| 何が変わり、なぜ review 可能か説明する | `change-package/v2` | diff scope、claim、evidence、waiver、policy decision を接続します。 |
| raw Codex / Claude Code / Copilot / human output を正規化する | `docs/agents/evidence-adapters.md` の fixture mapping、その後に既存 artifact | fixture は example であり contract ではありません。既存 generator / validator を使います。 |
| agent/session 間で作業を引き継ぐ | `ae-handoff/v1` | `docs/agents/handoff.md` と併用します。 |
| compact blocker と next action を producer に返す | `hook-feedback/v1` | `docs/agents/hook-feedback.md` と併用します。 |
| claim と supporting evidence を接続する | `claim-evidence-manifest/v1` | claim state は evidence lane と一致させます。 |
| policy gate judgment を記録する | `policy-decision/v1` | policy decision は judgment artifact であり raw log ではありません。 |
| fast-lane PR health を要約する | `verify-lite-run-summary` / `quality-scorecard` | required checks と PR comment の review input です。 |
