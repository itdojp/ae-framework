# Roadmap: DDD Intake Plan (includes #406–#411)

English / 日本語 (summary)

- Scope: execute Issues #406–#408 and extend plan with #409–#411 (DDD-friendly AE-IR, formal presets/BDD lint, domain events → contracts & replay).
- Milestones:
  - M1 (Q1): #409 + #410 + BDD lint wiring; docs and examples updated.
  - M2 (Q2): #411 replay/contract flow; CI artifacts normalization and PR summary aggregation.
- DoD (roll-up): traceId end-to-end; artifacts normalized to JSON; counterexamples as short GWT + JSON for `ae fix`; core stays thin (adapters optional).

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
