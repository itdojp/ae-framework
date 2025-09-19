# RFC: Composite Definition of Done (DoD) — policy-loader 合成 + 優先順位/厳しさマージ（policy > AE-IR > ae.config）

Status: Draft
Issue: #916

Summary
- Introduce a composite DoD computed from three sources: policy/quality.json, AE‑IR (optional dod), and ae.config.*
- Merge with “strictest wins” semantics per metric; precedence fallback: policy > AE‑IR > ae.config
- Provide a comparator expression spec (ops, units, normalization) reusable by #915
- Define conflict logging policy (logs + PR comment upsert with stable headers)
- Backward-compatible introduction with phased migration

Goals
- Single effective DoD visible to CI and local tools
- Central baseline in policy with spec intent (AE‑IR) and repo pragmatics (ae.config)
- Strictness cannot be weakened by lower layers; overridable upwards only

Scope
- In-repo policy-loader to read/compose: policy/quality.json, .ae/ae-ir.json, ae.config.*
- Effective DoD surfaced in: Verify Lite logs, coverage-check logs, and PR comments
- Non-goals: org-wide distribution/governance, secrets management

Terminology
- Strictest merge: choose the stricter value per metric; examples below
- Precedence fallback: when metrics are incomparable or missing → policy > AE‑IR > ae.config
- Enforcement order: strict > warn > off

**Policy Shape (quality.json) — Composite DoD anchors**
- Existing policy file provides categories, thresholds, enforcement, and environment overrides.
- This RFC standardizes gate references and clarifies thresholds for composite computation.

**Example (excerpt) — policy/quality.json**
```
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://ae-framework.com/schemas/quality-policy.json",
  "title": "AE-Framework Quality Gates Policy",
  "quality": {
    "coverage": {
      "description": "Code coverage requirements",
      "gates": ["coverage-check / gate", "verify-lite / coverage-note"],
      "enforcement": "strict",
      "thresholds": { "lines": 80, "functions": 80, "branches": 80, "statements": 80 },
      "tools": ["nyc", "vitest"],
      "phases": ["phase-3", "phase-4", "phase-5", "phase-6"]
    },
    "formal": {
      "gates": ["verify:conformance", "verify:alloy", "verify:tla", "verify:smt"],
      "enforcement": "warn",
      "thresholds": { "present": 1 }
    },
    "accessibility": {
      "gates": ["adapter-thresholds / a11y"],
      "enforcement": "strict",
      "thresholds": { "critical": 0, "serious": 2, "moderate": 3, "minor": 5, "total_warnings": 5 }
    },
    "lighthouse": {
      "gates": ["adapter-thresholds / lighthouse"],
      "enforcement": "warn",
      "thresholds": { "performance": 90, "accessibility": 95, "bestPractices": 85, "seo": 80, "pwa": "off" }
    }
  },
  "environments": {
    "ci": {
      "overrides": {
        "coverage.thresholds.lines": 85,
        "coverage.thresholds.functions": 85,
        "coverage.thresholds.statements": 85,
        "linting.thresholds.errors": 0
      }
    }
  }
}
```

**Composite Gate (optional) — references + evaluation**
```
{
  "quality": {
    "composite": {
      "description": "Composite DoD gate (evaluates normalized comparators)",
      "enforcement": "warn",           // may be strict/warn/off; strictest merge can elevate
      "refs": ["coverage", "formal", "accessibility", "lighthouse"],
      "evaluate": {
        "allOf": [
          { "id": "cov-lines",  "expr": "coverage.lines >= 85%" },
          { "id": "a11y-ser",   "expr": "accessibility.serious <= 0" },
          { "id": "lh-perf",    "expr": "lighthouse.performance >= 90%" },
          { "id": "formal-ok",  "expr": "formal.present >= 1" }
        ]
      }
    }
  }
}
```
Evaluation order
- Compute effective per-metric values via strictest merge.
- Normalize comparator operands (units); evaluate expressions in order; allOf must pass.
- Missing/incomparable metrics: apply precedence fallback (policy > AE‑IR > ae.config) and emit warn log.
- Composite gate’s enforcement is resolved by strictest enforcement across referenced categories and itself.

**AE‑IR Extension (optional; backward‑compatible)**
- Add an optional dod section expressing spec intent. Absent fields are ignored.

TypeScript shape (fragment)
```
export interface AEIR_DOD {
  enforcement?: 'off' | 'warn' | 'strict';
  coverage?: { enforcement?: 'off' | 'warn' | 'strict'; thresholds?: { lines?: number; functions?: number; branches?: number; statements?: number } };
  formal?:   { enforcement?: 'off' | 'warn' | 'strict'; gates?: Array<'conformance' | 'alloy' | 'tla' | 'smt'> };
  accessibility?: { enforcement?: 'off' | 'warn' | 'strict'; thresholds?: { critical?: number; serious?: number; moderate?: number; minor?: number; total_warnings?: number } };
  lighthouse?:   { enforcement?: 'off' | 'warn' | 'strict'; thresholds?: { performance?: number; accessibility?: number; bestPractices?: number; seo?: number; pwa?: number | 'off' } };
}
export interface AEIR { /* existing */ dod?: AEIR_DOD }
```

JSON fragment (example)
```
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

**ae.config (repo pragmatics)**
- Continue to support qa.coverageThreshold and similar knobs. These are lowest‑precedence on fallback and never soften stricter values from policy/AE‑IR under strictest merge.

**Strictest Merge Rule**
- Enforcement resolution: strict > warn > off; any strict yields strict effective enforcement.
- Coverage (higher is stricter): effective = max(policy, AE‑IR, ae.config) per key (lines, branches, functions, statements).
- A11y/Security budgets (lower is stricter): effective = min(policy, AE‑IR, ae.config).
- Incomparable metrics (unit/shape mismatch): fallback to precedence (policy > AE‑IR > ae.config) and log rationale.

Examples
- Coverage: policy lines ≥ 80, AE‑IR ≥ 85, ae.config ≥ 90 → effective lines ≥ 90
- Formal: policy=warn, AE‑IR=strict, ae.config=off → effective=strict
- A11y serious: policy ≤ 0, AE‑IR absent, ae.config ≤ 1 → effective ≤ 0
- Mismatch: AE‑IR dod.lighthouse.thresholds.pwa = "off" (categorical) vs policy numeric → use policy via precedence, log reason

**Conflict Logging Policy**
- Always log per‑metric source values and decision path.
- PR comment upsert with stable header (e.g., <!-- AE-DOD-COMPOSITE -->) shows:
  - Threshold (effective), Derived (by layer), Policy, Policy source
- In logs: include “fallback(precedence)” when unit/shape mismatch causes precedence to be used.
- Never downgrade stricter values; warn if a lower layer is attempting to soften a stricter policy value.

**Comparator Expression Spec (shared with #915)**
- Purpose: unify comparisons across gates with consistent ops/units and normalization.
- Expression forms:
  - JSON: { "metric": "coverage.lines", "op": ">=", "value": 90, "unit": "pct" }
  - String: "coverage.lines >= 90%"
- Operators: >, >=, <, <=, ==, !=
- Units and normalization:
  - pct: accept 0..100 (e.g., 90), 0..1 (e.g., 0.9), or string with % → canonical 0..100
  - count: non‑negative integer
  - time: ms/s/m/h accepted as "1500ms", "1.5s", "2m", "1h" → canonical ms (1s=1000ms, 1m=60000ms, 1h=3600000ms)
  - score: 0..100 (Lighthouse); if 0..1 given, multiply by 100
  - rps (throughput): accept "120rps", "120/s", "qps:120", "7200rpm" → canonical rps (rpm/60)
- Coercion examples:
  - "88%" → { unit: "pct", value: 88 }
  - 0.93 with unit pct → 93
  - "750ms" → 750; "1.5s" → 1500; "2m" → 120000; "1h" → 3600000
  - "7200rpm" → 120 rps; "120/s" → 120 rps; "qps:250" → 250 rps
- Comparison evaluation:
  - Normalize actual and target to canonical unit; apply op; produce tri‑state result { pass|fail, reason }
- Mapping to policy categories:
  - coverage.lines → pct (higher stricter)
  - accessibility.serious → count (lower stricter)
  - lighthouse.performance → score (higher stricter)

**Policy‑loader (composition)**
- Inputs: policy (with env overrides), AE‑IR.dod (optional), ae.config (optional)
- Steps:
  1) Load policy → apply environment overrides (e.g., ci)
  2) Extract per‑category thresholds/enforcement (policy layer)
  3) Read AE‑IR.dod and ae.config knobs (if present)
  4) Merge per metric using strictest rules; if incomparable, precedence fallback
  5) Emit effective DoD + derived values; log decisions and conflicts
- Output shape (example, coverage only):
```
{
  "effective": {
    "enforcement": "strict",
    "coverage": { "lines": 90, "functions": 90, "branches": 85, "statements": 90 }
  },
  "derived": {
    "policy":    { "coverage": { "lines": 80, "functions": 80, "branches": 80, "statements": 80 }, "enforcement": "strict" },
    "aeir":      { "coverage": { "lines": 88, "branches": 85 }, "enforcement": "warn" },
    "ae.config": { "coverage": { "lines": 90, "functions": 90, "statements": 90 } }
  },
  "decisions": [
    { "metric": "coverage.lines", "rule": "higher-stricter", "selected": 90, "from": "ae.config" },
    { "metric": "coverage.branches", "rule": "higher-stricter", "selected": 85, "from": "aeir" }
  ]
}
```

Log format (examples)
```
[composite] coverage.lines: policy=80, aeir=88, ae.config=90 -> effective=90 (rule=higher-stricter)
[composite] lighthouse.pwa: policy=off, aeir=off, ae.config=80 -> precedence=policy (categorical mismatch) [warn]
```

**Migration & Backward‑Compat**
- Phase 0 (visibility only): compute and print effective DoD in Verify Lite / coverage‑check logs; PR comment upsert. No gating changes.
- Phase 1 (coverage): use effective coverage thresholds in coverage‑check; still label‑gated enforcement (enforce‑coverage, coverage:<pct>) and main enforcement via repo vars.
- Phase 2 (formal, a11y, lighthouse): extend strictest merge; keep label‑gated enforcement; ensure no softening vs policy.
- AE‑IR dod is optional; existing AE‑IR remains valid.
- ae.config continues to work; treated as least‑precedence fallback and cannot override to weaken stricter baselines.
- policy/quality.json remains canonical; environment overrides still apply.

Acceptance rules (initial)
- Coverage: lines/functions/branches/statements must meet effective thresholds (strictest merge).
- Formal: presence gate satisfied (>=1), evaluation is warn by default; strict when any layer sets strict.
- Accessibility: serious <= effective threshold (often 0 in CI); other budgets as defined.
- Lighthouse: performance >= effective threshold (score normalized to 0..100).
- Composite (optional): all comparator expressions pass; logs derived/effective with precedence notes; PR comment upsert allowed.

**Open Questions**
- AE‑IR key name: dod vs quality — proposal keeps dod for scope clarity
- Comment headers: consolidate under <!-- AE-DOD-COMPOSITE --> or keep per‑gate headers (e.g., AE‑COVERAGE‑SUMMARY)
- Additional metrics to standardize in comparator spec (mutationScore, visual pixelDifference)

Appendix — File references
- policy file: policy/quality.json
- AE config: ae.config.ts
- Verify Lite workflow: .github/workflows/verify-lite.yml
- Coverage check: .github/workflows/coverage-check.yml
