# Spec Registry

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

仕様と関連アセットの正規配置ガイドです。TLA+（`spec/tla/`）、Alloy 6（`spec/alloy/`）、トレーススキーマ（`observability/trace-schema.yaml`）、ポリシー（Cedar）など。最小・合成可能・レビュー容易を原則とし、仮定と制約を明記します。

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
