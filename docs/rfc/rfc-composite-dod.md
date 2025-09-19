# RFC: Composite Definition of Done (DoD) with Strictest Merge

Status: Draft
Issue: #916

Summary
- Define a composite DoD computed from three sources: policy, AE‑IR, and ae.config
- Merge using “strictest wins” semantics with precedence clarity: policy > AE‑IR > ae.config
- Keep AE‑IR and repo config backward‑compatible; add optional fields only
- Surface the effective DoD in CI and PR comments, with Derived and Policy source notes

Motivation
- Centralize quality posture while allowing spec‑level intent (AE‑IR) and repo pragmatics (ae.config)
- Ensure PR checks and local tooling agree on one effective DoD
- Prefer safe defaults: stricter thresholds must never be weakened by lower layers

Scope
- In‑repo computation of an effective DoD for CI and local tooling
- Layers and sources:
  - Policy (central): `policy/quality.json` and policy engines under `policies/` (OPA/Cedar)
  - AE‑IR (spec intent): optional DoD hints inside AE‑IR
  - ae.config (repo pragmatics): local thresholds and toggles
- Non‑goals: external org policy delivery, secrets/governance, UI authoring

Terminology
- Strictest merge: choose the stricter value per metric/category. Examples:
  - Coverage minimum: higher is stricter → use max(source thresholds)
  - Vulnerability allowed counts: lower is stricter → use min(source thresholds)
  - Enforcement levels: strict > warn > off → use highest severity present

Design Overview
1) Policy layer provides baseline thresholds and enforcement (e.g., coverage, a11y, security).
   - See `policy/quality.json` for existing categories and environment overrides (e.g., `ci`).
     - Example references: `policy/quality.json:112`, `policy/quality.json:176`.
2) AE‑IR layer can declare spec‑level DoD intent (optional), without breaking existing AE‑IR.
3) ae.config remains supported; values are treated as the least authoritative in strictest merge.
4) Effective DoD is computed per metric by strictest merge across all present layers.

Merge Order and Semantics
- Presence/precedence: If a value is specified in multiple layers, compute strictest per metric.
- If metrics are incomparable (e.g., different unit/shape), fall back to precedence: policy > AE‑IR > ae.config.
- Enforcement resolution: strict > warn > off; any strict at any layer yields strict effective enforcement.
- Unknown/missing values: ignore missing; do not soften stricter values from other layers.

Schema Snippets
1) AE‑IR extension (backward‑compatible)
   - Add an optional `dod` section to AE‑IR. Example TypeScript and JSON Schema‑like structure:

```ts
// AE‑IR (extension proposal)
export interface AEIR_DOD {
  enforcement?: 'off' | 'warn' | 'strict';
  coverage?: {
    enforcement?: 'off' | 'warn' | 'strict';
    thresholds?: { lines?: number; functions?: number; branches?: number; statements?: number };
  };
  formal?: {
    enforcement?: 'off' | 'warn' | 'strict';
    gates?: Array<'conformance' | 'alloy' | 'tla' | 'smt'>;
  };
  accessibility?: {
    enforcement?: 'off' | 'warn' | 'strict';
    thresholds?: { critical?: number; serious?: number; moderate?: number; minor?: number; total_warnings?: number };
  };
  lighthouse?: {
    enforcement?: 'off' | 'warn' | 'strict';
    thresholds?: { performance?: number; accessibility?: number; bestPractices?: number; seo?: number; pwa?: number | 'off' };
  };
  security?: {
    enforcement?: 'off' | 'warn' | 'strict';
    thresholds?: { critical?: number; high?: number; moderate?: number; low?: number };
  };
  // extension point for adapters, mutation, linting, etc.
}

export interface AEIR { /* existing fields ... */ dod?: AEIR_DOD }
```

```json
// AE‑IR JSON (fragment)
{
  "version": "0.2",
  "metadata": { "name": "checkout" },
  "dod": {
    "enforcement": "strict",
    "coverage": { "thresholds": { "lines": 88, "branches": 85 } },
    "formal":   { "enforcement": "warn", "gates": ["conformance", "alloy"] }
  }
}
```

2) Policy shape (reference, existing)
- Quality gates policy already exists with thresholds and environment overrides; see:
  - `policy/quality.json:3`, `policy/quality.json:4` (ID/title)
  - `policy/quality.json:112` (policy section)
  - Coverage thresholds: `policy/quality.json:20`–`policy/quality.json:36`
  - CI overrides: `policy/quality.json:206`–`policy/quality.json:235`

3) Repo config (existing)
- `ae.config.ts:1` contains `qa.coverageThreshold` and other knobs respected locally and in CI.

Effective DoD Algorithm (strictest merge)
```ts
type Enforcement = 'off' | 'warn' | 'strict';
const rank: Record<Enforcement, number> = { off: 0, warn: 1, strict: 2 };

function strictestEnforcement(values: (Enforcement | undefined)[]): Enforcement | undefined {
  const present = values.filter(Boolean) as Enforcement[];
  if (!present.length) return undefined;
  return present.sort((a,b) => rank[b] - rank[a])[0];
}

// For metrics where higher is stricter (min coverage): use max
function strictestHigherIsStricter(values: (number | undefined)[]): number | undefined {
  const present = values.filter((v): v is number => typeof v === 'number');
  return present.length ? Math.max(...present) : undefined;
}

// For metrics where lower is stricter (max allowed issues): use min
function strictestLowerIsStricter(values: (number | undefined)[]): number | undefined {
  const present = values.filter((v): v is number => typeof v === 'number');
  return present.length ? Math.min(...present) : undefined;
}

// If incomparable (shape/unit mismatch), fall back to precedence: policy > AE‑IR > ae.config
```

Examples
1) Coverage (higher is stricter)
- policy: lines ≥ 80, AE‑IR: lines ≥ 85, ae.config: lines ≥ 90 → effective: lines ≥ 90

2) Formal enforcement
- policy: warn, AE‑IR: strict, ae.config: off → effective: strict

3) Accessibility budget (lower is stricter)
- policy: serious ≤ 0, AE‑IR: —, ae.config: serious ≤ 1 → effective: serious ≤ 0

4) Fallback to precedence
- AE‑IR asks for `pwa: "off"` (non‑numeric) and policy uses numeric score; shapes mismatch → use policy value

CI/UX Integration
- Verify Lite and PR comments display:
  - Threshold (effective), Derived (per‑layer), Policy/Policy source
  - Comment headers are stable and upserted, e.g., `<!-- AE-COVERAGE-SUMMARY -->`
- Label‑gated enforcement remains (e.g., `enforce-*`), but cannot soften policy baselines. Per‑PR overrides may raise thresholds; softening requires explicit policy‑override governance (out of scope here).

Migration Plan
- Phase 0: Compute and log effective DoD only (no gating change). Add notes in Verify Lite logs.
- Phase 1: Apply strictest merge for coverage in CI (verify‑lite, coverage‑check). Keep report‑only by default.
- Phase 2: Extend to formal/accessibility/lighthouse. Preserve label‑gated enforcement and environment overrides.

Backward Compatibility
- AE‑IR extension is optional; existing AE‑IR remains valid.
- `ae.config` continues to work; values are merged using strictest semantics.
- Policy JSON remains the canonical baseline. Environment overrides (e.g., CI) still apply.

Open Questions
- AE‑IR key name: `dod` vs `quality`? Proposal uses `dod` for clarity and limited scope.
- Cross‑repo/org policy distribution is out of scope; this RFC targets in‑repo computation.

Appendix: File References
- Policy file: `policy/quality.json:112`, `policy/quality.json:176`
- AE config: `ae.config.ts:1`

