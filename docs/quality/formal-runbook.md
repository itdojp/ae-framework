# Formal Runbook (low-impact start)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

負担の小さい形式検査の運用手順です。PR ラベルでの起動（`run-formal`）、手動トリガー、CLI スタブ、仕様/アーティファクトの配置、ロードマップ適合を簡潔にまとめています。

## English

### Usage (CI/Labels)
- Label-gated CI: add PR label `run-formal` to run formal checks (stub initially)
- Enforcement: add PR label `enforce-formal` to gate Apalache result (`ok==true`)
- Manual run: trigger `Formal Verify` via `workflow_dispatch`
  - inputs:
    - `target`: all|conformance|alloy|tla|smt
    - `engine`: tlc|apalache（tla用）
    - `solver`: z3|cvc5（smt用）
    - `alloyJar`: Alloy jar のパス（任意）
    - `tlaToolsJar`: tla2tools.jar のパス（任意）

### CLI Stubs (to be wired)
- `pnpm run verify:conformance` — prints stub; use `ae conformance verify` for real engine
- `pnpm run verify:alloy` — prints stub
- `pnpm run verify:tla -- --engine=apalache|tlc` — prints stub
- `pnpm run verify:smt -- --solver=z3|cvc5` — prints stub
- `pnpm run verify:formal` — 上記4種の連続実行（ローカル確認用）
  - 集計: `hermetic-reports/formal/summary.json` に要約を出力
  - 表示: 実行後にコンソールへ簡易サマリを表示

### Reproduce Locally / ローカル再現（要点）
- Tools check: `pnpm run tools:formal:check`（利用可能ツールの一覧）
- Apalache（ある場合）: `pnpm run verify:tla -- --engine=apalache`
- TLC（`TLA_TOOLS_JAR` がある場合）: `TLA_TOOLS_JAR=/path/to/tla2tools.jar pnpm run verify:tla -- --engine=tlc`
- SMT（z3/cvc5 がある場合）: `pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2`

Timeout（任意）
- 長時間実行を避けるため、TLA/SMT ランナーは `--timeout <ms>` をサポート（GNU `timeout` を利用可能な環境で有効）
- 例: `pnpm run verify:tla -- --engine=apalache --timeout 60000`
- なお、GNU `timeout` 使用時にタイムアウトが発生すると、summary の `status: "timeout"` となります（非ブロッキング運用）

Aggregate JSON の軽量検証（非ブロッキング）
- 集約ワークフローでは `artifacts/formal/formal-aggregate.json` を出力し、最小スキーマを警告レベルで検証します。
- ローカル確認: `node scripts/formal/validate-aggregate-json.mjs`（存在時に検証、欠損/不正は `::warning::` 出力）
- 1行サマリを表示する簡易CLI（ローカル）:
  - `node -e "const p='artifacts/formal/formal-aggregate.json';const j=require('fs').existsSync(p)?require('./'+p):null;if(!j){console.log('no aggregate');process.exit(0)}const pr=j.info?.present||{};const keys=Object.entries(pr).filter(([,v])=>v).map(([k])=>k);console.log('Present:', keys.length+'/5', keys.length?('('+keys.join(', ')+')'):'');"`
  - jq 例（presentCount/by-type）:
    - `jq '.info.presentCount' artifacts/formal/formal-aggregate.json`
    - `jq -r '.info.present | to_entries | map("\(.key)=\(.value|tostring)") | join(", ")' artifacts/formal/formal-aggregate.json`
  - ran/ok（Apalache の例）:
    - `jq -r '.info.ranOk.apalache' artifacts/formal/formal-aggregate.json`

Note（Aggregate comment wrapping）
- Long-line wrapping in the aggregate PR comment can be enabled via env `FORMAL_AGG_WRAP_WIDTH`.
- Default is OFF (no wrapping) to keep current look-and-feel; suggested values are `80`–`100` when enabling. Wrapping applies only outside code fences and preserves words.
- Tips: for tables/links with long URLs, prefer leaving wrap OFF to avoid visual breaks; code fences are never wrapped.
 - The aggregate JSON (`artifacts/formal/formal-aggregate.json`) is the single source of truth
   for presence/ran/ok; the PR comment is derived from it.

Keys quick reference (aggregate JSON)
- `info.present`: presence flags for tla/alloy/smt/apalache/conformance
- `info.presentCount`: number of present summaries (0..5)
- `info.ranOk.apalache`: `{ ran: boolean, ok: boolean|null }` (null = indeterminate)
  - jq: `jq '.info.ranOk.apalache' artifacts/formal/formal-aggregate.json`

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

### Minimal YAML (example)
```yaml
name: Formal Verify
on:
  pull_request:
    types: [labeled, synchronize]
jobs:
  verify:
    if: contains(github.event.pull_request.labels.*.name, 'run-formal')
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - run: pnpm run verify:formal
```

### Specs/Artifacts
- TLA+: `spec/tla/` (README with skeleton)
- Alloy 6: `spec/alloy/` (README with skeleton)
- Trace schema: `observability/trace-schema.yaml`
- Reports: `hermetic-reports/`（各ツールのsummary/出力を保存）
  - Apalache: `hermetic-reports/formal/apalache-summary.json`, `hermetic-reports/formal/apalache-output.txt`
  - Formal summary: `hermetic-reports/formal/summary.json`（present/conformance/smt/alloy/tla/apalache を含む）

### Samples
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
- `hermetic-reports/formal/summary.json`: 形式結果の集約（Conformance/SMT/Alloy/TLA/Apalache）
- `hermetic-reports/formal/tla-summary.json`: TLA ランナーの簡易要約（engine/file/status/output）
- `hermetic-reports/formal/alloy-summary.json`: Alloy ランナーの簡易要約（file/status/output）
- `hermetic-reports/formal/smt-summary.json`: SMT ランナーの簡易要約（solver/file/status/output）
- `hermetic-reports/conformance/summary.json`: Conformance 要約（events/schemaErrors/invariantViolations/violationRate/first/byType）

Artifacts のクイック確認（jq）
- 集約のpresence: `jq '.present' hermetic-reports/formal/summary.json`
- Conformance byType: `jq '.conformance.byType' hermetic-reports/formal/summary.json`
- 最初の不変違反: `jq '.conformance.firstInvariantViolation' hermetic-reports/formal/summary.json`

Keys quick reference（aggregate JSON）
- `info.present`: 各レポートの有無（tla/alloy/smt/apalache/conformance）
- `info.presentCount`: present の合計数（0..5）
- `info.ranOk.apalache`: `{ ran: boolean, ok: boolean|null }`（null は不確定）
  - jq 例: `jq '.info.ranOk.apalache' artifacts/formal/formal-aggregate.json`

Field リファレンス（抜粋）
- `formal/summary.json`
  - `timestamp`: 集計時刻（ISO8601）
  - `present`: 各セクションの有無（conformance/smt/alloy/tla）
  - `conformance` / `smt` / `alloy` / `tla`: 各ランナーのサマリ（存在時）
- `conformance/summary.json`
  - `input`: 入力イベントファイル（相対パス）
  - `events`: イベント数
  - `schemaErrors`: スキーマ違反件数
  - `invariantViolations`: 不変違反件数
  - `violationRate`: 不変違反率（違反数/イベント数）
  - `firstInvariantViolation`: 最初の不変違反（例: `type`, `index`）
  - `firstSchemaError`: 最初のスキーマ違反（例: `path`, `message`）
  - `byType`: 不変タイプ別の件数（例: `onhand_min`, `allocated_le_onhand`）
- `tla-summary.json`
  - `engine`: `tlc` | `apalache`
  - `file`: 対象TLAファイル
  - `status`: `ran` | `tool_not_available` | `file_not_found` など
- `apalache-summary.json`
  - `tool`: `apalache`
  - `ran`: 実行の有無（true/false）
  - `ok`: 成否（true/false/null=不確定）
  - `version`, `timeMs`, `toolPath`, `run`, `errorCount`, `errors[]`, `errorSnippet{before,after,lines[]}` など
- `alloy-summary.json`
  - `file`: 対象Alloyファイル
  - `status`: `ran` | `tool_not_available` | `file_not_found` など
- `smt-summary.json`
  - `solver`: `z3` | `cvc5`
  - `file`: 対象SMT-LIBファイル
  - `status`: `ran` | `solver_not_available` | `file_not_found` など

### Roadmap Fit (Issue #493)
- Non‑blocking, label‑gated CI first
- Wire real engines behind the above stubs incrementally

---

## 日本語（詳細）

### 運用の基本
1) PR でフォーマル検査を走らせたい場合は、ラベル `run-formal` を付与（初期はスタブ）。
2) 手動実行は GitHub Actions の `workflow_dispatch`（Formal Verify）から起動。

### CLI スタブ（配線予定）
- `pnpm run verify:conformance` — スタブ出力（実行時は `ae conformance verify` を利用）
- `pnpm run verify:alloy` — スタブ出力
- `pnpm run verify:tla -- --engine=apalache|tlc` — スタブ出力
- `pnpm run verify:smt -- --solver=z3|cvc5` — スタブ出力
- `pnpm run verify:formal` — 上記4種の連続実行（ローカル確認）

### 仕様/成果物配置
- TLA+: `spec/tla/`（最小スケルトンあり）
- Alloy 6: `spec/alloy/`（最小スケルトンあり）
- トレーススキーマ: `observability/trace-schema.yaml`
- レポート（計画）: `hermetic-reports/`

### 環境変数（出力の調整）
- verify-apalache.mjs（要約の整形）
  - `APALACHE_ERRORS_LIMIT`（既定 5）: errors[] に採用する最大行数
  - `APALACHE_ERROR_LINE_CLAMP`（既定 200）: 1行の最大表示幅（超過時は末尾に`…`）
  - `APALACHE_SNIPPET_BEFORE` / `APALACHE_SNIPPET_AFTER`（既定 2/2）: エラースニペットの前後行数
- formal-aggregate.yml（PR コメントの整形）
  - `FORMAL_AGG_LINE_CLAMP`（既定 200）: コメントに表示する1行の最大幅
  - `FORMAL_AGG_ERRORS_LIMIT`（既定 5）: エラー行の最大件数
  - `FORMAL_AGG_SNIPPET_MAX_LINES`（既定 20）: エラースニペット（前後文脈を含む）の最大行数
  - コメント末尾に `Generated: <ISO8601>` を付与（生成時刻）

いずれも未設定時は既定値で動作し、非ブロッキングです。

### サンプル
- TLA+: `spec/tla/DomainSpec.tla` — 最小の不変/遷移
- Alloy: `spec/alloy/Domain.als` — 最小のアサーション

### ロードマップ（Issue #493）
- まずは非ブロッキングでラベル起動（PR 体験を阻害しない）
- 各エンジン（Conformance/Alloy/TLA+/SMT）を段階的に実配線

### CI 配線例（YAML 抜粋）
```yaml
name: Formal Verify
on:
  pull_request:
    types: [labeled, synchronize]
jobs:
  verify:
    if: contains(github.event.pull_request.labels.*.name, 'run-formal')
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - run: pnpm run verify:formal
```

### Makefile Snippet（任意）
```make
.PHONY: verify-formal
verify-formal:
	pnpm run verify:formal
```
- `artifacts/formal/formal-aggregate.json`: PR向け集約（byType/present/ranOk 等の最小情報を含む）
