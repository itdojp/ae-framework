# Formal Runbook (low-impact start)

Usage
- Label-gated CI: add PR label `run-formal` to run formal checks (stub initially)
- Manual run: trigger `Formal Verify` via `workflow_dispatch`

CLI stubs (to be wired)
- `pnpm run verify:conformance` — prints stub; use `ae conformance verify` for real engine
- `pnpm run verify:alloy` — prints stub
- `pnpm run verify:tla -- --engine=apalache|tlc` — prints stub
- `pnpm run verify:smt -- --solver=z3|cvc5` — prints stub
 - `pnpm run verify:formal` — 上記4種の連続実行（ローカル確認用）

Specs/Artifacts
- TLA+: `spec/tla/` (README with skeleton)
- Alloy 6: `spec/alloy/` (README with skeleton)
- Trace schema: `observability/trace-schema.yaml`
- Reports (planned): `hermetic-reports/`

Samples
- TLA+: `spec/tla/DomainSpec.tla`（最小の安全性不変と遷移の例）
- Alloy: `spec/alloy/Domain.als`（最小の安全性アサーションの例）

Roadmap Fit (Issue #493)
- Non‑blocking, label‑gated CI first
- Wire real engines behind the above stubs incrementally
