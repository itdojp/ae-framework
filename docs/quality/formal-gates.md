# Formal Quality Gates (v0.2 DoD)

This document defines the formal verification gates that must pass in CI for v0.2.

Objectives
- Conformance checking between runtime traces and formal specs
- Lightweight temporal verification via Alloy 6 (LTL + past operators)
- TLA+ verification via TLC and Apalache (SMT/BMC + inductive invariants)
- Redundant SMT solving with Z3 and cvc5

CI Targets (green = pass)
- verify:conformance — trace vs spec conformance
- verify:alloy — Alloy 6 temporal properties
- verify:tla --engine=apalache|tlc — TLA+ model checking
- verify:smt --solver=z3|cvc5 — solver redundancy

Workflow
1) Failing property yields a counterexample
2) Counterexample becomes a failing test under tests/
3) Apply minimal fix until all gates return green

Artifacts
- Trace schema: observability/trace-schema.yaml
- Reports: hermetic-reports/conformance/

Status
- v0.2: Establish gates as stubs in CI; incrementally wire real engines

