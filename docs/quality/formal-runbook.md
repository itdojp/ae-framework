---
docRole: ssot
lastVerified: '2026-03-10'
owner: formal-methods
verificationCommand: pnpm -s run check:doc-consistency
---
# Formal Runbook (low-impact start)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

負担の小さい形式検査の運用手順です。PR ラベルでの起動（`run-formal`）、手動トリガー、CLI スタブ、仕様/アーティファクトの配置、ロードマップ適合を簡潔にまとめています。
全ツールのスモークテスト手順は `docs/quality/formal-full-run.md` を参照してください。

## English

### Usage (CI/Labels)
- Label-gated CI: add PR label `run-formal` to run formal checks (stub initially)
- Enforcement: add PR label `enforce-formal` to gate Apalache result (`ok==true`)
- Manual run: trigger `Formal Verify` via `workflow_dispatch`
  - inputs:
    - `target`: all|conformance|alloy|tla|smt|apalache|kani|spin|csp|lean
    - `engine`: tlc|apalache（tla用）
    - `solver`: z3|cvc5（smt用）
    - `alloyJar`: Alloy jar のパス（任意）
    - `tlaToolsJar`: tla2tools.jar のパス（任意）
Full smoke test instructions: `docs/quality/formal-full-run.md`.

### CLI Runners (non-blocking)
- `pnpm run verify:conformance` — conformance summary runner（必要に応じて `ae conformance verify` と併用）
- `pnpm run verify:alloy` — Alloy runner（`ALLOY_RUN_CMD` / `ALLOY_JAR` / `alloy` CLI を利用）
- `pnpm run verify:tla -- --engine=apalache|tlc` — TLA runner（`TLA_TOOLS_JAR` または `apalache` を利用）
- `pnpm run verify:smt -- --solver=z3|cvc5` — SMT runner
- `pnpm run verify:kani` — Kani 検出ランナー（presence summary）
- `pnpm run verify:spin` — Promela/SPIN runner
- `pnpm run verify:csp` — CSP runner（`CSP_RUN_CMD`/`cspx`/`refines`/`cspmchecker`）
  - `cspx` 使用時は `csp-summary.json` と `cspx-result.json` を出力
  - `schema_version=0.1` 非互換は `status: "unsupported"` として記録
  - Details (artifacts / example outputs): `docs/quality/formal-csp.md`
- `pnpm run verify:lean` — Lean4 `lake build` runner
- `pnpm run verify:formal` — 上記の連続実行（ローカル確認用、non-blocking）
  - 集計: `artifacts/hermetic-reports/formal/summary.json` に要約を出力
  - 表示: 実行後にコンソールへ簡易サマリを表示

### Runtime Hooks（PObserve 型）取り込み（Phase 2.2）
- ランタイムフック JSON を（任意で）`artifacts/hermetic-reports/runtime/hooks.json` に保存し、ドライバーが再生サマリと突き合わせます。
- 環境変数:
  - `RUNTIME_HOOKS` または `CONFORMANCE_RUNTIME_HOOKS` — フック JSON のパス
  - `CONFORMANCE_TRACE` — リプレイサマリ（既定: `artifacts/domain/replay.summary.json`）
- conformance-summary には `runtimeHooks: {present, path, count, uniqueEvents[], traceId, matchesReplayTraceId}` が追加されます。

### BDD → LTL プロパティ候補（レポートのみ）
- `pnpm run bdd:suggest` で `spec/bdd/**/*.feature`（フォールバック: `features/`）から GWT を抽出し、LTL 候補を出力します。
  - 出力: 
    - `artifacts/bdd/scenarios.json` — PRサマリ用の {title, criteriaCount}
    - `artifacts/properties/ltl-suggestions.json` — {count, items[]}（集約/参考用）

### Reproduce Locally / ローカル再現（要点）
- Tools check: `pnpm run tools:formal:check`（利用可能ツールの一覧）
- Apalache（ある場合）: `pnpm run verify:tla -- --engine=apalache`
- TLC（`TLA_TOOLS_JAR` がある場合）: `TLA_TOOLS_JAR=/path/to/tla2tools.jar pnpm run verify:tla -- --engine=tlc`
- SMT（z3/cvc5 がある場合）: `pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2`
 
### Apalache Quickstart（任意）
- Presence/version check: `node scripts/formal/check-apalache.mjs`
- Verify (non-blocking summary): `node scripts/formal/verify-apalache.mjs --file spec/tla/DomainSpec.tla`
- 同名の `*.cfg`（例: `spec/tla/DomainSpec.cfg`）が存在する場合、ランナーは自動で `--config` を適用
- Notes:
  - formal-verify に非ブロッキングの presence/version ガードステップを追加済み（verify:apalache）
  - aggregate コメントには Apalache ran/ok とエラー断片を一行で要約（長行は折り返し／トリム）

Timeout（任意）
- 長時間実行を避けるため、TLA/SMT ランナーは `--timeout <ms>` をサポート（GNU `timeout` を利用可能な環境で有効）
- 例: `pnpm run verify:tla -- --engine=apalache --timeout 60000`
- なお、GNU `timeout` 使用時にタイムアウトが発生すると、summary の `status: "timeout"` となります（非ブロッキング運用）

### Troubleshooting（よくある確認ポイント）
- PATH: `apalache` または `apalache-mc` が見つからない場合は `node scripts/formal/check-apalache.mjs` で存在/バージョンを確認
- Timeout: 長時間のログが出続ける場合は `--timeout` を設定し、aggregate コメントの `status: "timeout"` を目安に切り上げ
- CSP unsupported:
  - `artifacts/hermetic-reports/formal/csp-summary.json` の `status` が `"unsupported"` で、`output` または `outputFile`（例: `artifacts/hermetic-reports/formal/csp-output.txt`）に `--summary-json` に関する CLI エラー（例: `unexpected argument`, `unknown argument`, `wasn't expected` 等）が含まれる場合、`cspx` が古く互換性がありません（`cspx typecheck --help | grep -- --summary-json` で確認し、`docs/quality/formal-tools-setup.md` のピン留め手順で更新。代替として `CSP_RUN_CMD` も利用可能）
  - `schema_version mismatch` の場合は `cspx-result.json` の `schema_version` を確認し、現行の契約（`schema_version=0.1`）に合わせて `cspx` を更新してください
  - 詳細: `docs/quality/formal-csp.md`
- Logs: 生ログは `artifacts/hermetic-reports/formal/<tool>-output.txt` に保存（例: `apalache-output.txt`, `tla-output.txt`, `smt-output.txt`, `alloy-output.txt`, `spin-output.txt`, `csp-output.txt`, `lean-output.txt`）
  - Formal Summary v1/v2（`artifacts/formal/formal-summary-v1.json` / `artifacts/formal/formal-summary-v2.json`）の `results[].logPath` は、ログが存在する場合にそのパス（repo-relative）を設定します

Advanced toggles（運用向け）
- Aggregate wrap 幅: `FORMAL_AGG_WRAP_WIDTH`（0=無効、推奨 80–100）
- Apalache エラー抽出の上限/長行トリム: `APALACHE_ERRORS_LIMIT` / `APALACHE_ERROR_LINE_CLAMP`（既定: 5 / 200）
- Apalache 出力プレビュー長: `APALACHE_OUTPUT_CLAMP`（既定: 4000）
  - `artifacts/hermetic-reports/formal/apalache-summary.json` の `output` に適用（不足時は値を増やす）
Aggregate JSON の軽量検証（非ブロッキング）
- 集約ワークフローでは `artifacts/formal/formal-aggregate.json` を出力し、最小スキーマを警告レベルで検証します。
- ローカル確認: `node scripts/formal/validate-aggregate-json.mjs`（存在時に検証、欠損/不正は `::warning::` 出力）

Formal Summary v1/v2（dual-write + dual-validate / 段階導入）
- producer: `scripts/formal/generate-formal-summary-v1.mjs`（`--out` で v1、`--out-v2` で v2）を使用し、`.github/workflows/verify-lite.yml` と `.github/workflows/formal-aggregate.yml` で並行出力します。
- 出力:
  - `artifacts/formal/formal-summary-v1.json`（スキーマ: `schema/formal-summary-v1.schema.json`）
  - `artifacts/formal/formal-summary-v2.json`（スキーマ: `schema/formal-summary-v2.schema.json`、`schemaVersion=formal-summary/v2`、`contractId=formal-summary.v2`）
- dual-validate（ローカル）:
  - `node scripts/ci/validate-formal-summary-v1.mjs artifacts/formal/formal-summary-v1.json schema/formal-summary-v1.schema.json`
  - `node scripts/ci/validate-formal-summary-v2.mjs artifacts/formal/formal-summary-v2.json schema/formal-summary-v2.schema.json`
- dual-validate（CI）: `scripts/ci/validate-artifacts-ajv.mjs` が v1/v2 をともに検証し、`.github/workflows/formal-aggregate.yml` の strict（`enforce-formal`）では v1/v2 を `--require` で必須化します。
- consumer: `scripts/ci/generate-run-manifest.mjs` が `formalSummaryV1` / `formalSummaryV2` として参照します。
- 1行サマリを表示する簡易CLI（ローカル）:
  - `node -e "const p='artifacts/formal/formal-aggregate.json';const j=require('fs').existsSync(p)?require('./'+p):null;if(!j){console.log('no aggregate');process.exit(0)}const pr=j.info?.present||{};const keys=Object.entries(pr).filter(([,v])=>v).map(([k])=>k);const total=(typeof j.info?.presentTotal==='number')?j.info.presentTotal:Object.keys(pr).length;console.log('Present:', keys.length+'/'+total, keys.length?('('+keys.join(', ')+')'):'');"`
  - jq 例（presentCount/by-type）:
    - `jq '.info.presentCount' artifacts/formal/formal-aggregate.json`
    - `jq '.info.presentTotal' artifacts/formal/formal-aggregate.json`
    - `jq -r '.info.present | to_entries | map("\(.key)=\(.value|tostring)") | join(", ")' artifacts/formal/formal-aggregate.json`
  - ran/ok（Apalache の例）:
    - `jq -r '.info.ranOk.apalache' artifacts/formal/formal-aggregate.json`

Note（Aggregate comment wrapping）
- Enable with env `FORMAL_AGG_WRAP_WIDTH`（既定: OFF/無効）
- 推奨値: 80–100（有効化する場合）。コードフェンス内は対象外、語単位で折返し。
- Tips: 長いURLや表が多い場合は OFF を推奨（見た目が崩れる可能性）

Wrap pros/cons（quick ref）
- Pros: 長文行の可読性向上、横スクロール回避
- Cons: 表/URLの視覚崩れの可能性（表やURLが多い場合は無効推奨）

Single source of truth
- Aggregate JSON `artifacts/formal/formal-aggregate.json` が present/ran/ok の唯一の正とし、PRコメントはそこから生成

Keys quick reference (aggregate JSON)
- `info.present`: presence flags for tla/alloy/smt/apalache/conformance/kani/spin/csp/lean
- `info.presentCount`: number of present summaries
- `info.presentTotal`: total number of tracked summaries (denominator)
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
- `pnpm run conformance:report` — 既存の `artifacts/conformance/conformance-results.json` や `artifacts/hermetic-reports/conformance/*.json` を集約し `reports/conformance/verify-lite-summary.(json|md)` を生成
- `pnpm bdd` — 暗号化チャットの BDD シナリオ（デバイス登録・セッション・鍵ローテーション）を実行し、`artifacts/bdd/encrypted-chat/*.json` にスナップショットを保存
- `pnpm pipelines:pact` — Pact 契約テストを実行し、暗号化チャット API 契約（`tests/contracts/encrypted-chat-contracts.test.ts`）を検証

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
- Reports: `artifacts/hermetic-reports/`（各ツールのsummary/出力を保存）
  - Apalache: `artifacts/hermetic-reports/formal/apalache-summary.json`, `artifacts/hermetic-reports/formal/apalache-output.txt`
  - Formal summary: `artifacts/hermetic-reports/formal/summary.json`（present/conformance/smt/alloy/tla/apalache を含む）
  - `metadata`: `generatedAtUtc`, `generatedAtLocal`, `timezoneOffset`, `gitCommit`, `branch`, `runner`, `toolVersions`
  - Conformance aggregated summary (verify-lite): `reports/conformance/verify-lite-summary.json` / `reports/conformance/verify-lite-summary.md`

### Samples
- TLA+: `spec/tla/DomainSpec.tla`（最小の安全性不変と遷移の例）
- Alloy: `spec/alloy/Domain.als`（最小の安全性アサーションの例）

 
Tools
- ローカル確認: `pnpm run tools:formal:check`（インストール済みツールを一覧）
- セットアップ手順: [formal-tools-setup.md](./formal-tools-setup.md)
- 運用パターン/CI 分割: [formal-ops-guidelines.md](./formal-ops-guidelines.md)
- トレース検証（軽量）: `pnpm run trace:validate`（サンプルイベントのスキーマ整合を確認）
 - SMT サンプル: `spec/smt/sample.smt2`（動作確認用）
 - 実行例: `pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2`
  - Alloy/TLA jar の設定: workflow_dispatch で `alloyJar` / `tlaToolsJar` を指定、またはローカルで `ALLOY_JAR` / `TLA_TOOLS_JAR` を設定

verify:conformance オプション
- `-i, --in <file>` 入力イベントJSON（既定: `samples/conformance/sample-traces.json`）
- `--schema <file>` トレーススキーマYAML（既定: `observability/trace-schema.yaml`）
- `--out <file>` 出力先（既定: `artifacts/hermetic-reports/conformance/summary.json`）
- `--disable-invariants <list>` 無効化する不変（`,`区切り。`allocated_le_onhand,onhand_min`）
- `--onhand-min <number>` onHand の最小値（既定: 0）

補足
- `samples/conformance/sample-traces.json` はリポジトリに同梱されています（`verify:conformance` / `trace:validate` の既定入力）。

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
 - Alloy 6 CLI（exec）を使う場合は `ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}'` を設定

Tips（出力・色・抑制）
- コンソール要約は色分け表示。色を無効化するには `NO_COLOR=1` を指定（CI等）
- 実行ログのサマリは `artifacts/hermetic-reports/formal/summary.json` でも確認可能
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
     - `target=all`（または個別: conformance|alloy|tla|smt|apalache|kani|spin|csp|lean）
     - `engine`（tla: tlc|apalache）
     - `solver`（smt: z3|cvc5）
     - `alloyJar`/`tlaToolsJar`（ツールJarパス／環境によって指定）
     3. 結果は: コンソール要約（logs）、`formal-reports` アーティファクトに集約

Artifacts（Formal Reports）
- `artifacts/hermetic-reports/formal/summary.json`: 形式結果の集約（Conformance/SMT/Alloy/TLA/Apalache/Kani/SPIN/CSP/Lean）
- `artifacts/formal/formal-summary-v1.json`: Formal Summary v1（normalized）
- `artifacts/formal/formal-summary-v2.json`: Formal Summary v2（`schemaVersion=formal-summary/v2`, `contractId=formal-summary.v2`）
- `artifacts/hermetic-reports/formal/tla-summary.json`: TLA ランナーの簡易要約（engine/file/status/output）
- `artifacts/hermetic-reports/formal/alloy-summary.json`: Alloy ランナーの簡易要約（file/status/output）
- `artifacts/hermetic-reports/formal/smt-summary.json`: SMT ランナーの簡易要約（solver/file/status/output）
- `artifacts/hermetic-reports/formal/apalache-summary.json`: Apalache ランナーの簡易要約（ran/ok/errors/snippet/outputFile）
- `artifacts/hermetic-reports/formal/kani-summary.json`: Kani 検出の要約（detected/version）
- `artifacts/hermetic-reports/formal/spin-summary.json`: SPIN ランナーの簡易要約（file/ltl/status/output）
- `artifacts/hermetic-reports/formal/csp-summary.json`: CSP ランナーの簡易要約（file/backend/status/resultStatus/exitCode/detailsFile/output）
- `artifacts/hermetic-reports/formal/cspx-result.json`: cspx の実行結果（cspx 使用時）
- `artifacts/hermetic-reports/formal/lean-summary.json`: Lean4 ランナーの簡易要約（project/status/output）
- `artifacts/hermetic-reports/conformance/summary.json`: Conformance 要約（events/schemaErrors/invariantViolations/violationRate/first/byType）

Artifacts のクイック確認（jq）
- 集約のpresence: `jq '.present' artifacts/hermetic-reports/formal/summary.json`
- Conformance byType: `jq '.conformance.byType' artifacts/hermetic-reports/formal/summary.json`
- 最初の不変違反: `jq '.conformance.firstInvariantViolation' artifacts/hermetic-reports/formal/summary.json`

Keys quick reference（aggregate JSON）
- `info.present`: 各レポートの有無（tla/alloy/smt/apalache/conformance/kani/spin/csp/lean）
- `info.presentCount`: present の合計数
- `info.presentTotal`: 追跡対象の総数（分母）
- `info.ranOk.apalache`: `{ ran: boolean, ok: boolean|null }`（null は不確定）
  - jq 例: `jq '.info.ranOk.apalache' artifacts/formal/formal-aggregate.json`

Field リファレンス（抜粋）
- `artifacts/hermetic-reports/formal/summary.json`
  - `present`: 各セクションの有無（conformance/smt/alloy/tla/apalache/kani/spin/csp/lean など）
  - `conformance` / `smt` / `alloy` / `tla` / `apalache`: 各ランナーのサマリ（存在時）
- `artifacts/formal/formal-summary-v1.json`
  - `results[]`: normalized result entry（`status` / `reason` / `code` / `logPath` など）
- `artifacts/formal/formal-summary-v2.json`
  - top-level: `schemaVersion=formal-summary/v2`, `contractId=formal-summary.v2`
  - `results[]`: v2 normalized result entry（`status` / `reason` / `code` / `logPath` など）
- `formal/summary.json`
  - legacy compatibility input。current canonical path ではない
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
- レポート（計画）: `artifacts/hermetic-reports/`

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
