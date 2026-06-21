# Sample Issue: add reviewer guidance for reservation audit notes

## Intended scope

Update the reviewer-facing documentation for the reservation audit sample and add
one focused unit test that demonstrates the documented audit note. The change is
expected to stay within:

- `docs/inventory/reservation-audit.md`
- `tests/unit/inventory/reservation-audit.test.ts`
- `examples/assurance-control-plane/scope-drift-demo/**`

## Explicit non-goals

- Do not rewrite inventory domain logic.
- Do not touch payment, settlement, migration, or deployment policy files.
- Do not introduce a new agent-specific approval vocabulary.

## Reviewer question

If the producer reports extra changed files, treat that as scope-drift evidence
for reviewer disposition. Do not call it a proof failure by itself.
