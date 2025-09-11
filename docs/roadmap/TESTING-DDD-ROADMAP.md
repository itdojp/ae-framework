# Roadmap: Testing + DDD Intake Plan (#406–#411)

English / 日本語 (summary)

- Scope: Testing enhancements (#406–#408) and DDD intake (#409–#411).
- Milestones:
  - M1 (Q1): #406–#408 (test additions) + #409 + #410 (DDD IR & presets/BDD lint); docs/examples updated.
  - M2 (Q2): #411 (domain events → contracts/replay); CI artifacts normalization and PR summary aggregation.
- DoD (roll-up): traceId end-to-end; artifacts normalized to JSON; counterexamples as short GWT + JSON for `ae fix`; core stays thin (adapters optional).

## Tracks

### A. Testing Enhancements (#406–#408)
- #406: minimal property-based testing support; persist {seed, runs, version} to `artifacts/properties/summary.json`.
- #407: format formal counterexamples into short GWT + machine-readable JSON for `ae fix`; include `traceId` and minimal repro.
- #408: official adapter templates; normalize external tool outputs to `artifacts/*/summary.json`; keep adapters optional.

### B. DDD Intake (#409–#411)
- #409: AE-IR optional fields (boundedContext/aggregate/domainEvents/ubiquitousTerms) — backward compatible.
- #410: formal presets for aggregate invariants + BDD step lint (When → Aggregate Root commands only).
- #411: domain events → Zod contracts & replay fixtures; verify invariants via `npm run test:replay`.

## Issue Checklist

- [ ] #406 feat: introduce minimal property-based testing support — https://github.com/itdojp/ae-framework/issues/406
- [ ] #407 feat: format counterexamples into Given-When-Then scenarios — https://github.com/itdojp/ae-framework/issues/407
- [ ] #408 docs/ci: provide official adapter templates for external testing tools — https://github.com/itdojp/ae-framework/issues/408
- [ ] #409 feat: AE-IR optional fields for DDD (boundedContext/aggregate/domainEvents) — https://github.com/itdojp/ae-framework/issues/409
- [ ] #410 feat: formal presets for aggregate invariants + BDD step lint — https://github.com/itdojp/ae-framework/issues/410
- [ ] #411 feat: domain events → contracts & replay fixtures — https://github.com/itdojp/ae-framework/issues/411

## Artifacts and Policies

- property: `artifacts/properties/summary.json` ({seed, runs, version})
- adapters: `artifacts/*/summary.json`
- formal: `formal/summary.json`
- events: `artifacts/domain/events.json`
- PR summary aggregates: coverage, failing GWT, adapter summaries (one page)
- BDD lint: `When` limited to Aggregate Root commands

## Links

- Epic #383 — https://github.com/itdojp/ae-framework/issues/383
- PR #303 (discussion thread)

## References
- Property summary schema (#406): docs/schemas/artifacts-properties-summary.schema.json
- CLI focus flag (#406/#411): docs/reference/cli-focus-traceid.md
- Formal summary schema (#407): docs/schemas/formal-summary.schema.json
- Counterexample → GWT format (#407): docs/quality/counterexample-gwt.md
- Adapter normalization (#408): docs/templates/adapters/README.md
- Adapter summary schema (#408): docs/schemas/artifacts-adapter-summary.schema.json
- Domain events schema (#411): docs/schemas/domain-events.schema.json
- Example events: examples/inventory/artifacts/domain/events.sample.json

- DDD IR fields: docs/ddd/ae-ir-ddd.md
- Domain events → contracts/replay: docs/ddd/events.md
- Property-based harness: docs/testing/property-harness.md

## References
- See also: docs/roadmap/TESTING-DDD-INDEX.md (reviewer quick links)
