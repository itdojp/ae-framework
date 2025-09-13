# Formal Runbook (low-impact start)

Usage
- Label-gated CI: add PR label `run-formal` to run formal checks (stub initially)
- Manual run: trigger `Formal Verify` via `workflow_dispatch`
  - inputs:
    - `target`: all|conformance|alloy|tla|smt
    - `engine`: tlc|apalache（tla用）
    - `solver`: z3|cvc5（smt用）
    - `alloyJar`: Alloy jar のパス（任意）
    - `tlaToolsJar`: tla2tools.jar のパス（任意）

CLI stubs (to be wired)
- `pnpm run verify:conformance` — prints stub; use `ae conformance verify` for real engine
- `pnpm run verify:alloy` — prints stub
- `pnpm run verify:tla -- --engine=apalache|tlc` — prints stub
- `pnpm run verify:smt -- --solver=z3|cvc5` — prints stub
- `pnpm run verify:formal` — 上記4種の連続実行（ローカル確認用）
  - 集計: `hermetic-reports/formal/summary.json` に要約を出力
  - 表示: 実行後にコンソールへ簡易サマリを表示

ログ例（label: run-formal 実行時）
```
--- Formal Summary ---
Conformance: schemaErrors=0, invariantViolations=1, rate=0.333, first=allocated_le_onhand@2
SMT: ran
Alloy: tool_not_available
TLA: tool_not_available (tlc)
----------------------
```

色の意味（コンソール要約）
- 緑: OK（実行成功・違反なし）
- 黄: 注意（違反やスキップなど）
- 灰: ツール未検出など情報のみ

ステータス基準（Normalized Status）
- Conformance: `[OK]` if `schemaErrors=0` 且つ `invariantViolations=0`、それ以外は `[WARN]`
- SMT: 実行できたら `[OK]`（status=`ran`）、ソルバー未検出は `[INFO]`、その他は `[WARN]`
- Alloy: 実行できたら `[OK]`（status=`ran`）、ツール未検出は `[INFO]`、その他は `[WARN]`
- TLA: 実行できたら `[OK]`（status=`ran`）、ツール未検出は `[INFO]`、その他は `[WARN]`

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
 - SMT サンプル: `spec/smt/sample.smt2`（動作確認用）
 - 実行例: `pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2`
  - Alloy/TLA jar の設定: workflow_dispatch で `alloyJar` / `tlaToolsJar` を指定、またはローカルで `ALLOY_JAR` / `TLA_TOOLS_JAR` を設定

verify:conformance オプション
- `-i, --in <file>` 入力イベントJSON（既定: `samples/conformance/sample-traces.json`）
- `--schema <file>` トレーススキーマYAML（既定: `observability/trace-schema.yaml`）
- `--out <file>` 出力先（既定: `hermetic-reports/conformance/summary.json`）
- `--disable-invariants <list>` 無効化する不変（`,`区切り。`allocated_le_onhand,onhand_min`）
- `--onhand-min <number>` onHand の最小値（既定: 0）

Roadmap Fit (Issue #493)
- Non‑blocking, label‑gated CI first
- Wire real engines behind the above stubs incrementally

サマリの見方（conformance）
- `events`: 入力イベント数
- `schemaErrors`: スキーマ違反件数
- `invariantViolations`: 不変違反件数（`violationRate` は events に対する比率）
- `firstInvariantViolation`: 最初の違反（`type` と `index`）
 - `byType(...)`: 不変タイプごとの件数（例: `onhand_min`, `allocated_le_onhand`）

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
  
Alloy CLI（環境がある場合）
- `pnpm run verify:alloy -- --file spec/alloy/Domain.als`
- CLI が無い場合は `ALLOY_JAR=/path/to/alloy.jar` を設定し、`java -jar $ALLOY_JAR spec/alloy/Domain.als`

Tips（出力・色・抑制）
- コンソール要約は色分け表示。色を無効化するには `NO_COLOR=1` を指定（CI等）
- 実行ログのサマリは `hermetic-reports/formal/summary.json` でも確認可能
- PRサマリにも Formal summary を1行で表示（サマリが生成されている場合）
- `file_not_found`: `--file` の指定パスを確認（SMT/TLA/Alloy）
 - コンソール要約の抑制: `QUIET=1` を指定で print-summary を抑止（CIログを簡潔にしたい場合）

PRサマリの表示例
```
• Formal summary: [WARN] Conformance: schemaErrors=0, invariantViolations=3, rate=0.300, first=allocated_le_onhand@2, firstSchemaPath=/state/onHand, byType(onhand_min=1, allocated_le_onhand=2); [OK] SMT: ran; [INFO] Alloy: tool_not_available; [INFO] TLA: tool_not_available (tlc)
```

Formal Verify の実行（target=all）
- ラベル実行（PR上）
  1. 対象PRに `run-formal` ラベルを付与
  2. CIが起動し、Formal Verify が label-gated で実行（非ブロッキング）
  3. 結果は: コンソール要約（logs）、`formal-reports` アーティファクト、PRサマリの Formal 行に反映
- 手動実行（Actions > Formal Verify）
  1. Actions タブで `Formal Verify` を選択し `Run workflow`
  2. inputs（任意）
     - `target=all`（または個別: conformance|alloy|tla|smt）
     - `engine`（tla: tlc|apalache）
     - `solver`（smt: z3|cvc5）
     - `alloyJar`/`tlaToolsJar`（ツールJarパス／環境によって指定）
  3. 結果は: コンソール要約（logs）、`formal-reports` アーティファクトに集約

Artifacts（Formal Reports）
- `hermetic-reports/formal/summary.json`: 形式結果の集約（Conformance/SMT/Alloy/TLA）
- `hermetic-reports/formal/tla-summary.json`: TLA ランナーの簡易要約（engine/file/status/output）
- `hermetic-reports/formal/alloy-summary.json`: Alloy ランナーの簡易要約（file/status/output）
- `hermetic-reports/formal/smt-summary.json`: SMT ランナーの簡易要約（solver/file/status/output）
- `hermetic-reports/conformance/summary.json`: Conformance 要約（events/schemaErrors/invariantViolations/violationRate/first/byType）

Artifacts のクイック確認（jq）
- 集約のpresence: `jq '.present' hermetic-reports/formal/summary.json`
- Conformance byType: `jq '.conformance.byType' hermetic-reports/formal/summary.json`
- 最初の不変違反: `jq '.conformance.firstInvariantViolation' hermetic-reports/formal/summary.json`
