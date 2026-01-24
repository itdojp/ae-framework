# Research Survey for ae-framework (Issue 1062)

## Snapshot
- Date: 2026-01-24
- Source: [GitHub Issue #1062](https://github.com/itdojp/ae-framework/issues/1062)

## Goal
Provide a concise map of relevant research to ae-framework phases and highlight
adoption or design-modification opportunities.

## Paper map (condensed)

| Paper | Year/Venue | Phases | Adoption idea | Notes |
| --- | --- | --- | --- | --- |
| PAT-Agent | ASE 2025 | Formal, Verify | Planning→Coding→ModelCheck→Repair loop | PAT-centric; needs verifier adapter |
| TiCoder | FSE 2022 | Intent, Tests, Code | Tests-first intent formalization | Tests alone insufficient |
| Agentic Programming Survey | 2024 | All | Define metrics: cost/tokens/memory/turns | High-level taxonomy |
| FormalCoder | 2024 | Formal, Code, Verify | NL→Spec→MC→Code chain | Alloy bias |
| VerifAI | NeurIPS 2024 | Code, Verify | Counterexample-guided repair | Runtime cost |
| TestPilot | ICSE 2024 | Tests | Autonomous test maintenance | Large-scale validation TBD |
| CodeRanker | 2023 | Tests, Code | Test-guided reranking | Best for unit scopes |
| AutoTLA | 2024 | Formal | NL→TLA+ templates | Public artifacts vary |
| ConformanceCheck++ | AAAI 2025 | Verify, Operate | Runtime conformance checks | Limited case studies |
| AgentBench | 2023 | Cross-cutting | Multi-agent role evaluation | Not FM-focused |

## Adopt vs Modify (summary)

### Adopt
- Autoformalize loop (Planning→Coding→ModelCheck→Repair)
- Tests-first intent (TiCoder + TestPilot)
- Test-guided reranking (CodeRanker)
- Closed-loop verification/repair (VerifAI)
- Runtime conformance checks (ConformanceCheck++)
- Agentic metrics in req2run

### Modify
- Verifier adapter layer for TLC/Apalache and portability
- Normalize Planning/Coding/Verifying agent roles
- Unified Verify stage (tests + formal + runtime)
- Formal plan contract (`formal.yaml`) between Planning/Coding

## Follow-up checklist (from Issue 1062, proposed)
- Docs: phase alignment in README + docs/phases
- Verifier adapter: TLC/Apalache + unified counterexample JSON
- Autoformalize (planned CLI): `ae formal:auto`
- Tests-first default (planned CLI): `ae tests:suggest` + `ae code:rank-by-tests`
- Autoverify (planned CLI): `ae code:autoverify`
- Runtime (planned CLI): `verify:conformance` + `ae operate:monitor`
- Benchmark: req2run metrics extension
