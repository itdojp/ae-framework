# Issue: Standardize Spec Tooling (OpenAPI) and JIT Domain Assets

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

OpenAPI 等の高頻度テンプレートはリポジトリに事前配置し、ドメイン固有の資産は JIT（AI 支援）で生成する方針。spec-as-input を中心に、CI 連携・アーティファクト配置・受け入れ基準を定義します。

Context
- OpenAPI is a standard format to describe RESTful APIs. In this repo, it serves as an input for code generation (routes/models/server), runtime contract checks (contracts-exec), and downstream contract/E2E test scaffolding.
- Question raised: Do we need to pre-provide tools/templates (like OpenAPI) per domain/type, or can AI/JIT handle it? What else should be prepared?

Summary (Decision)
- Provide repo-level, high-frequency templates upfront (OpenAPI, JSON Schema, TLA+/Alloy skeletons, BDD feature skeletons, CI runners). These reduce friction and standardize inputs.
- Rely on JIT (just-in-time) generation for domain-specific artifacts (e.g., domain invariants, sample data, authority models), with AI assisting synthesis and refinement.
- Keep the pipeline centered on “spec-as-input”. OpenAPI is the most common, so we keep a minimal template readily available and wire CI to auto-detect it.

Why this works
- Standard inputs → consistent codegen + verification + traceability.
- JIT for domain specifics → avoids premature over-preparation; AI can generalize and fill details incrementally.

Scope
- In-scope: RESTful API flows (OpenAPI), formal checks scaffolding (TLC/Alloy), runtime contracts skeletons, BDD traceability.
- Out-of-scope (now): Full enforcement gates for formal checks by default; advanced domain-specific libraries.

Provide upfront (repo-level templates)
- API/Comm:
  - OpenAPI minimal template (YAML/JSON) under `artifacts/codex/openapi.yaml` (or `specs/openapi/*.yaml`).
  - JSON Schema base folder if needed later (`schemas/json/`).
- Formal verification:
  - TLA+ minimal module skeleton (Init/Next/Spec/Property) under `specs/formal/tla+/`.
  - Alloy minimal skeleton (sig/assert/check) under `specs/formal/alloy/`.
- Runtime contracts:
  - `src/contracts/` skeleton files (`schemas.ts`, `conditions.ts`, `machine.ts`).
- BDD/Traceability:
  - Gherkin Feature/Scenario template with tag/slug guidance under `specs/bdd/features/`.
- CI
  - Verify workflow runs traceability, TLC/Alloy (report-only), and contracts presence/exec. Docs explain env toggles and labels.

JIT (AI-assisted) per domain/product
- Domain invariants (e.g., no negative stock, idempotency), refined into pre/post conditions and formal properties.
- Sample data/fixtures synthesized from OpenAPI schemas; expanded as scenarios grow.
- Authorization models (roles/permissions) and policy stubs when needed.
- Additional interface definitions (AsyncAPI, GraphQL SDL, Protobuf) only if the solution requires them.

Recommended locations
- `artifacts/codex/openapi.yaml|json` (default lookup by contracts-exec)
- `specs/openapi/`, `specs/formal/tla+/`, `specs/formal/alloy/`, `specs/bdd/features/`
- `src/contracts/` for runtime contracts

CI implications (current state)
- PR summary shows: traceability totals, linked examples, TLC/Alloy success rate, and contracts presence/exec results.
- Label `enforce-contracts` (or env `CONTRACTS_ENFORCE=1`) optionally gates PRs on minimal contract checks.
- Alloy execution is optional (provide `ALLOY_JAR` to enable). Failure detection is tunable via `ALLOY_FAIL_REGEX`.

Acceptance criteria
- A minimal OpenAPI template lives in the repo and is referenced in docs; CI can use it for contracts-exec input synthesis.
- Templates for TLA+/Alloy and BDD exist or are trivial to add; verify workflow already integrates them (report-only).
- Docs clearly state: what is pre-provided, what is JIT, where to place files, and how PR summaries reflect results.

Follow-ups (optional small PRs)
- Add `artifacts/codex/openapi.yaml` with a minimal inventory-reservation example (3 endpoints + schemas).
- Generate and commit `src/contracts/` skeletons so contracts-check is green and contracts-exec can report parse/pre/post.
- Add optional label `enforce-formal` to gate on TLC/Alloy once specs mature.

Labels
- `area:specs`, `area:ci`, `type:enhancement`, `priority:normal`
