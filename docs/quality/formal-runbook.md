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

Conformance sample (quick demo)
- `pnpm run conformance:sample` — サンプルのルール/設定/データ/コンテキストを生成
- `pnpm run conformance:verify:sample` — 生成データで検証を実行（JSONレポート出力）

Specs/Artifacts
- TLA+: `spec/tla/` (README with skeleton)
- Alloy 6: `spec/alloy/` (README with skeleton)
- Trace schema: `observability/trace-schema.yaml`
- Reports (planned): `hermetic-reports/`

Samples
- TLA+: `spec/tla/DomainSpec.tla`（最小の安全性不変と遷移の例）
- Alloy: `spec/alloy/Domain.als`（最小の安全性アサーションの例）

Tools
- ローカル確認: `pnpm run tools:formal:check`（インストール済みツールを一覧）
- セットアップ手順: [formal-tools-setup.md](./formal-tools-setup.md)
- トレース検証（軽量）: `pnpm run trace:validate`（サンプルイベントのスキーマ整合を確認）

verify:conformance オプション
- `-i, --in <file>` 入力イベントJSON（既定: `samples/conformance/sample-traces.json`）
- `--schema <file>` トレーススキーマYAML（既定: `observability/trace-schema.yaml`）
- `--out <file>` 出力先（既定: `hermetic-reports/conformance/summary.json`）
- `--disable-invariants <list>` 無効化する不変（`,`区切り。`allocated_le_onhand,onhand_min`）
- `--onhand-min <number>` onHand の最小値（既定: 0）

Roadmap Fit (Issue #493)
- Non‑blocking, label‑gated CI first
- Wire real engines behind the above stubs incrementally

TLA+/Apalache/SMT コマンド例（ローカル）
- TLA+ (TLC)
  - `java -cp $TLA_TOOLS_JAR tlc2.TLC spec/tla/DomainSpec.tla`
  - 失敗時はログを確認（`TLC FAILED`/`Invariant violated` など）
- Apalache
  - `apalache-mc version`
  - `apalache-mc check --inv=Invariant spec/tla/DomainSpec.tla`
- SMT（単体動作確認）
  - `z3 --version` / `cvc5 --version`
  - 実運用では CLI から `verify:smt -- --solver=z3|cvc5` を経由
