# Spec Registry

Canonical locations for specifications and related assets.

Locations
- TLA+: `spec/tla/`
- Alloy 6: `spec/alloy/`
- Runtime Trace Schema: `observability/trace-schema.yaml`
- Policy (Cedar): `policies/cedar/`

Conventions
- Keep specs minimal, composable, and reviewable
- Prefer property-first modeling (safety, liveness)
- Record assumptions and known limitations per spec

Roadmap
- Wire `verify:conformance` against trace schema
- Add `verify:alloy` and `verify:tla` engines
- Enable `verify:smt` with z3 and cvc5

