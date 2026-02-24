# Spec Registry

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

仕様と関連アセットの正規配置ガイドです。TLA+（`spec/tla/`）、Alloy 6（`spec/alloy/`）、トレーススキーマ（`observability/trace-schema.yaml`）、ポリシー（Cedar）など。最小・合成可能・レビュー容易を原則とし、仮定と制約を明記します。

Canonical locations for specifications and related assets.

Locations
- Context Pack v1: `spec/context-pack/`
- Context Pack functor map: `spec/context-pack/functor-map.json`
- Context Pack functor map schema: `schema/context-pack-functor-map.schema.json`
- Context Pack natural transformation map: `spec/context-pack/natural-transformations.json`
- Context Pack natural transformation schema: `schema/context-pack-natural-transformation.schema.json`
- Context Pack product/coproduct map: `spec/context-pack/product-coproduct-map.json`
- Context Pack product/coproduct schema: `schema/context-pack-product-coproduct.schema.json`
- Context Pack Phase5+ template map: `spec/context-pack/phase5-templates.json`
- Context Pack Phase5+ template schema: `schema/context-pack-phase5-templates.schema.json`
- TLA+: `spec/tla/`
- Alloy 6: `spec/alloy/`
- SMT-LIB2: `spec/smt/`
- SPIN/Promela: `spec/spin/`
- CSP: `spec/csp/`
- Lean4: `spec/lean/`
- Formal examples (refinement/mappings): `spec/formal/`
- BDD (GWT): `spec/bdd/` (fallback: `features/`)
- Properties (LTL/PBT seeds): `spec/properties/`
- Runtime Trace Schema: `observability/trace-schema.yaml`
- Policy (Cedar): `policies/cedar/`

Conventions
- Keep specs minimal, composable, and reviewable
- Prefer property-first modeling (safety, liveness)
- Record assumptions and known limitations per spec

Roadmap
- Keep CI runs non-blocking; evolve toolchains incrementally (see `docs/quality/formal-runbook.md`)
- Context Pack validation details: `docs/spec/context-pack.md`
- Context Pack Phase5+ cookbook: `docs/guides/context-pack-phase5-cookbook.md`
- Context Pack troubleshooting runbook: `docs/operations/context-pack-troubleshooting.md`
