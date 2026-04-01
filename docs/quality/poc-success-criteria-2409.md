---
docRole: derived
canonicalSource:
- docs/quality/verify-first-implementation-runbook.md
- docs/quality/verification-gates.md
lastVerified: '2026-04-02'
---
# PoC Success Criteria (#2409 first slice: TS baseline vs Go/Rust)

> Language / 言語: English | 日本語

---

## English

### Purpose
- Define machine-verifiable adoption criteria for comparing the TypeScript baseline with Go and Rust candidates under identical conditions.

### Preconditions (as of 2026-03-04)
- Node.js: `>=20.11 <23` (`package.json` `engines.node`)
- pnpm: `10.0.0` (`package.json` `packageManager`)
- Comparison targets: `TS baseline`, `Go candidate`, `Rust candidate`
- Use the same input data, scenarios, and measurement scripts for every candidate.

### 1. Measurement Protocol
- Scenarios: `small`, `medium`, and `large`.
  - Record the fixed input counts in the comparison template.
- Repetitions: `2` warm-up runs and `10` measured runs for each implementation and scenario.
- Measurements: `throughput (req/s)`, `p95 latency (ms)`, `error rate (%)`, `peak RSS (MB)`, `cold start (ms)`.
- Machine-readable TS baseline output: `artifacts/reference/benchmarks/bench.json`.
  - Schema: `schema/benchmark-report.schema.json`
  - Primary metric keys: `metrics.p95`, `metrics.errorRate`, `metrics.coldStartMs`, `metrics.peakRssMb`
- Aggregation rule: use the median as the primary metric and compute variation as `CV = stddev / mean`.
- Baseline ratio: `ratio = candidate / ts_baseline`
  - Latency improvement (smaller is better): `latency_improvement = (1 - ratio) * 100`
  - Throughput improvement (larger is better): `throughput_improvement = (ratio - 1) * 100`

### 2. Success Criteria (quantitative and machine-checkable)

| Category | Metric | Passing threshold | Decision weight |
| --- | --- | --- | --- |
| Performance | `p95 latency ratio` | `<= 0.85` (at least 15% improvement vs TS) | Required |
| Performance | `throughput ratio` | `>= 1.20` (at least 20% improvement vs TS) | Required |
| Performance | `error rate` | `<= max(0.5, TS + 0.2pt)` | Required |
| Performance | `peak RSS ratio` | `<= 1.15` | Required |
| Reproducibility | `CV(p95 latency)` / `CV(throughput)` | both `<= 0.05` | Required |
| Reproducibility | Output consistency | checksum match rate `= 100%` under identical input | Required |
| Implementation cost | PoC implementation effort | `<= 15` person-days including design, implementation, verification, and documentation | Required |
| Implementation cost | Bring-up time | a new team member can reproduce the local benchmark in `<= 45` minutes | Required |
| Operational delta | CI runtime increase | `<= +15%` vs current TS operation | Required |
| Operational delta | Monitoring compatibility | missing existing SLO metrics (`latency`, `error`, `throughput`) `= 0` | Required |
| Operational delta | Security delta | new Critical vulnerabilities `= 0` | Required |
| Reference | `cold start ratio` | `<= 1.10` | Reference |

### 3. Go / No-Go Rules
- **Go**: all required criteria pass and no withdrawal rule in Section 4 applies.
- **Conditional Go**: all required criteria pass, but only reference metrics miss targets. Document the improvement plan and deadline (maximum two sprints) in the ADR.
- **No-Go**: any required criterion fails, or any withdrawal rule applies.

### 4. Withdrawal Criteria (early stop / reject)
Withdraw a candidate immediately when any of the following conditions is met.

1. Two consecutive measurement cycles miss at least two required performance criteria.
2. Any reproducibility criterion (`CV` or checksum match) fails even once.
3. The implementation effort is forecast to exceed `20` person-days including remaining work.
4. The CI operational delta exceeds `+25%` and there is no credible mitigation path.
5. A P1-equivalent incident or a Critical vulnerability cannot be resolved.

### 5. Required Evidence
- Comparison measurements: record them with `docs/templates/quality/poc-comparison-metrics-template.md`.
- Decision record: capture the adoption decision with `docs/templates/quality/adr-poc-adoption-template.md`.
- TS baseline execution command: `pnpm exec tsx src/cli.ts bench`
- Note: `src/cli.ts` is a legacy compatibility shim that preserves `benchmark-report/v1`. The canonical main CLI entrypoint is `src/cli/index.ts`, and the benchmark-specific CLI is `src/cli/benchmark-cli.ts` (`ae-benchmark`).
- TS baseline outputs:
  - machine-readable: `artifacts/reference/benchmarks/bench.json`
  - human-readable: `artifacts/reference/benchmarks/bench.md`
- Always attach the executed command, commit SHA, measurement timestamp, and execution environment (CPU / memory / OS / runtime).

#### 5.1 Comparison Command (bench.json -> ratios / pass-fail)
Use `benchmark-report/v1` (`artifacts/reference/benchmarks/bench.json`) as the input and generate ratios plus required-threshold decisions mechanically.

```bash
node scripts/quality/bench-compare.mjs \
  --baseline artifacts/bench-ts-run1.json,artifacts/bench-ts-run2.json \
  --candidate go=artifacts/bench-go-run1.json,artifacts/bench-go-run2.json \
  --candidate rust=artifacts/bench-rust-run1.json,artifacts/bench-rust-run2.json \
  --criteria configs/bench-criteria.default.json \
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

When comparing multiple runs, standardize the run set before passing it to `bench-compare`.

```bash
# Collect a run set first (for example: artifacts/bench-ts-run1.json, artifacts/bench-ts-run2.json, ...)
node scripts/ci/bench-runset.mjs \
  --out artifacts/bench-ts-runset.txt \
  --min-runs 2 \
  artifacts/bench-ts-run*.json

# Use the collected runset as the baseline
RUNSET="$(cat artifacts/bench-ts-runset.txt)"
node scripts/quality/bench-compare.mjs \
  --baseline "${RUNSET}" \
  --candidate go=artifacts/bench-go-run1.json,artifacts/bench-go-run2.json \
  --candidate rust=artifacts/bench-rust-run1.json,artifacts/bench-rust-run2.json \
  --criteria configs/bench-criteria.default.json \
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

- JSON output: `artifacts/bench-compare.json`
- Markdown output: `artifacts/bench-compare.md`
- Baseline runset file: `artifacts/bench-ts-runset.txt`
- Criteria file: `configs/bench-criteria.default.json`
  - Schema: `schema/bench-criteria.schema.json`
- Required checks:
  - `p95 ratio <= 0.85`
  - `throughput ratio >= 1.20`
  - `error rate <= max(0.5, baseline + 0.2pt)`
  - `peak RSS ratio <= 1.15`
- Reproducibility checks:
  - `p95 CV <= 0.05`
  - `throughput CV <= 0.05`
  - applies when `runCount >= 2`
- Output consistency check: `checksum match rate == 100%`
- Reference check: `cold start ratio <= 1.10`

#### 5.1.1 Evidence Generation in the Nightly Monitor (report-only)
- The nightly monitor uses `artifacts/bench-ts-runset.txt` and executes `bench-compare` in report-only mode.
- Example command inside the nightly workflow:

```bash
RUNSET="$(cat artifacts/bench-ts-runset.txt)"
node scripts/quality/bench-compare.mjs \
  --baseline "${RUNSET}" \
  --candidate ts-self="${RUNSET}" \
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

- Because `ts-self` is a self-comparison, it cannot satisfy the improvement thresholds `p95 ratio <= 0.85` and `throughput ratio >= 1.20`; therefore `overall` is expected to be `fail`.
- That `overall` result is not used as an action gate in the nightly monitor. The monitor focuses on `reproducibility` (`CV` and checksum) plus trend evidence.
- The current temporary operation uses both `compare-bench.mjs` (two-point comparison with a 5% allowance) and `bench-compare` (report-only).

#### 5.1.2 Monitor Operating Policy (`compare-bench` coexistence and `fail-on-threshold-breach`)
- Current report-only mode:
  - Deviation detection continues to use `compare-bench.mjs` (`<= 5%`).
  - `bench-compare` JSON / Markdown outputs are stored as nightly artifacts.
- Preconditions before enabling `--fail-on-threshold-breach`:
  - `bench-runset` (at least two runs) is collected continuously for the last 14 days without gaps.
  - `reproducibility` (`p95 CV`, `throughput CV`, `checksum`) remains stable for 7 consecutive days and noise-driven failures stay within the accepted band.
  - Switching conditions (enable / disable and rollback steps) are documented in the operations procedure.
- Once the prerequisites are met, gate the `bench-compare` result in stages within the `monitor` job: first warning-only, then fail-on-breach.

#### 5.1.3 Artifact Inspection Steps When Nightly Fails
1. Open the failed `Nightly Matrix` run in GitHub Actions and confirm that the `Upload artifacts` step in the `monitor` job completed.
2. Download `nightly-artifacts` from the run and inspect `artifacts/bench-ts-compare.json`.
   - `ok: false` or `rows[].pass: false` identifies threshold deviations detected by `compare-bench.mjs` (two-point comparison with 5% allowance).
3. Check `artifacts/bench-ts-runset.txt` and `artifacts/bench-ts-run*.json` to verify that the compared runs were selected correctly.
4. If `artifacts/bench-compare.json` or `artifacts/bench-compare.md` exists, use them as supplemental evidence for reproducibility (`CV`, checksum) and trend review.

#### 5.2 Primary Data Sources and Calculation Rules (locked)
- Input contract: `benchmark-report/v1`
  - Schema: `schema/benchmark-report.schema.json`
- Criteria contract: `bench-criteria/v1`
  - Default: `configs/bench-criteria.default.json`
  - Schema: `schema/bench-criteria.schema.json`
- Metric mapping:
  - `p95 latency` = `metrics.p95`
  - `error rate` = `metrics.errorRate`
  - `cold start` = `metrics.coldStartMs`
  - `peak RSS` = `metrics.peakRssMb`
  - `throughput` = `sum(summary[].hz)` with non-empty `summary` and `hz > 0`
- Ratio rule: `ratio = candidate / baseline`
  - Threshold direction: upper bound for `p95`, `cold start`, and `peak RSS`; lower bound for `throughput`
  - If the baseline value is `<= 0`, treat the ratio as `null` (non-applicable) and do not force that ratio check to fail.
- Reproducibility rule: `CV = stddev / mean`
  - `p95 CV`: computed from multi-run `metrics.p95`
  - `throughput CV`: computed from multi-run `sum(summary[].hz)`
  - If only one run exists, `CV` is `null` (non-applicable)
- Checksum match rate: normalize `schemaVersion + summary + metrics` from each `benchmark-report/v1` run (stable key order; `summary` sorted by name), then compare `sha256` digests against the first run.
- Error-rate upper bound: `max(0.5, baseline.errorRate + 0.2)` (percentage points)
- Comparison output contract: `artifacts/bench-compare.json`
  - `schemaVersion: bench-compare/v1`
  - Schema: `schema/bench-compare.schema.json`

### 6. Mapping to Issue #2409 Checklist

| Item in `#2409 first slice` | Supporting document |
| --- | --- |
| 1) Define PoC success criteria | `docs/quality/poc-success-criteria-2409.md` |
| 2) Add the comparison measurement template | `docs/templates/quality/poc-comparison-metrics-template.md` |
| 3) Add the ADR template | `docs/templates/quality/adr-poc-adoption-template.md` |
| 4) Minimal docs index update | `docs/README.md`, `docs/templates/quality/README.md` |

---

## 日本語

### 目的
- TypeScript baseline と Go/Rust 候補を同一条件で比較し、採用/不採用を機械的に判定できる基準を定義する。

### 前提条件（2026-03-04時点）
- Node.js: `>=20.11 <23`（`package.json` の `engines.node`）
- pnpm: `10.0.0`（`package.json` の `packageManager`）
- 比較対象: `TS baseline` / `Go candidate` / `Rust candidate`
- 同一入力データ・同一シナリオ・同一計測スクリプトで比較する。

### 1. 計測プロトコル
- シナリオ: `small` / `medium` / `large` の3段階。
  - 入力件数の固定値は比較テンプレートに記録する。
- 反復回数: 各実装・各シナリオでウォームアップ2回 + 本計測10回。
- 計測値: `throughput(req/s)`, `p95 latency(ms)`, `error rate(%)`, `peak RSS(MB)`, `cold start(ms)`。
- TS baseline の機械可読成果物: `artifacts/reference/benchmarks/bench.json`。
  - schema: `schema/benchmark-report.schema.json`
  - 主要指標キー: `metrics.p95`, `metrics.errorRate`, `metrics.coldStartMs`, `metrics.peakRssMb`
- 集計方法: 中央値（median）を主指標、ばらつきは `CV = stddev / mean` で算出する。
- ベースライン比: `ratio = candidate / ts_baseline`
  - latency 改善率（小さいほど良い）: `latency_improvement = (1 - ratio) * 100`
  - throughput 改善率（大きいほど良い）: `throughput_improvement = (ratio - 1) * 100`

### 2. 成功基準（定量・判定可能）

| 区分 | 指標 | 合格基準 | 判定 |
| --- | --- | --- | --- |
| 性能 | `p95 latency ratio` | `<= 0.85`（TS比 15%以上改善） | 必須 |
| 性能 | `throughput ratio` | `>= 1.20`（TS比 20%以上改善） | 必須 |
| 性能 | `error rate` | `<= max(0.5, TS + 0.2pt)` | 必須 |
| 性能 | `peak RSS ratio` | `<= 1.15` | 必須 |
| 再現性 | `CV(p95 latency)` / `CV(throughput)` | いずれも `<= 0.05` | 必須 |
| 再現性 | 出力整合 | 同一入力で checksum 一致率 `= 100%` | 必須 |
| 実装コスト | PoC実装工数 | `<= 15` 人日（設計/実装/検証/文書化を含む） | 必須 |
| 実装コスト | 立ち上げ時間 | 新規メンバーが `<= 45` 分でローカル計測を再現 | 必須 |
| 運用差分 | CI実行時間増分 | 既存TS運用比 `<= +15%` | 必須 |
| 運用差分 | 監視項目互換 | 既存SLO指標（latency/error/throughput）欠落 `= 0` | 必須 |
| 運用差分 | セキュリティ差分 | 新規 Critical 脆弱性 `= 0` | 必須 |
| 参考 | `cold start ratio` | `<= 1.10` | 参考 |

### 3. Go / No-Go ルール
- **Go**: 必須基準を全て充足し、撤収条件（第4章）に該当しない。
- **Conditional Go**: 必須基準を充足しつつ、参考指標のみ未達。改善計画と期限（最大2スプリント）を ADR に明記する。
- **No-Go**: 必須基準を1つでも未達、または撤収条件に該当する。

### 4. 撤収条件（早期中止・不採用）
以下のいずれかを満たした時点で当該候補は撤収（不採用）とする。

1. 2回連続計測で性能必須基準を2項目以上未達。
2. 再現性基準（CVまたはchecksum一致）を1回でも満たせない。
3. 実装工数が `20` 人日を超過見込み（残作業見積を含む）。
4. CI運用差分が `+25%` を超え、改善策の見込みがない。
5. 重大障害（P1相当）または Critical 脆弱性が解消不能。

### 5. 証跡（必須成果物）
- 比較計測結果: `docs/templates/quality/poc-comparison-metrics-template.md` を使用して記録する。
- 判定記録: `docs/templates/quality/adr-poc-adoption-template.md` を使用して ADR 化する。
- TS baseline 実行コマンド: `pnpm exec tsx src/cli.ts bench`
- 補足: `src/cli.ts` は `benchmark-report/v1` 互換を維持する legacy compatibility shim。メイン CLI の canonical entrypoint は `src/cli/index.ts`、ベンチマーク専用 CLI は `src/cli/benchmark-cli.ts`（`ae-benchmark`）。
- TS baseline 出力:
  - 機械可読: `artifacts/reference/benchmarks/bench.json`
  - 人間可読: `artifacts/reference/benchmarks/bench.md`
- 実行ログには、コマンド、使用コミットSHA、計測日時、実行環境（CPU/メモリ/OS/ランタイム）を必ず添付する。

#### 5.1 比較判定コマンド（bench.json -> 比率/合否）
`benchmark-report/v1`（`artifacts/reference/benchmarks/bench.json`）を入力に、PoC比較の比率と必須閾値判定を機械的に生成する。

```bash
node scripts/quality/bench-compare.mjs \
  --baseline artifacts/bench-ts-run1.json,artifacts/bench-ts-run2.json \
  --candidate go=artifacts/bench-go-run1.json,artifacts/bench-go-run2.json \
  --candidate rust=artifacts/bench-rust-run1.json,artifacts/bench-rust-run2.json \
  --criteria configs/bench-criteria.default.json \
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

複数 run を比較する場合は、run 群を先に標準化してから `bench-compare` に渡す。

```bash
# run群（例: artifacts/bench-ts-run1.json, artifacts/bench-ts-run2.json, ...）を収集
node scripts/ci/bench-runset.mjs \
  --out artifacts/bench-ts-runset.txt \
  --min-runs 2 \
  artifacts/bench-ts-run*.json

# 収集済み runset を baseline として使用
RUNSET="$(cat artifacts/bench-ts-runset.txt)"
node scripts/quality/bench-compare.mjs \
  --baseline "${RUNSET}" \
  --candidate go=artifacts/bench-go-run1.json,artifacts/bench-go-run2.json \
  --candidate rust=artifacts/bench-rust-run1.json,artifacts/bench-rust-run2.json \
  --criteria configs/bench-criteria.default.json \
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

- 出力 JSON: `artifacts/bench-compare.json`
- 出力 Markdown: `artifacts/bench-compare.md`
- baseline runset file: `artifacts/bench-ts-runset.txt`
- 判定 criteria: `configs/bench-criteria.default.json`
  - schema: `schema/bench-criteria.schema.json`
- 必須判定:
  - `p95 ratio <= 0.85`
  - `throughput ratio >= 1.20`
  - `error rate <= max(0.5, baseline + 0.2pt)`
  - `peak RSS ratio <= 1.15`
- 再現性判定:
  - `p95 CV <= 0.05`
  - `throughput CV <= 0.05`
  - `runCount >= 2` の場合に適用する
- 出力整合判定: `checksum match rate == 100%`
- 参考判定: `cold start ratio <= 1.10`

#### 5.1.1 Nightly monitor での証跡生成（report-only）
- nightly monitor では `artifacts/bench-ts-runset.txt` を使って `bench-compare` を report-only で実行する。
- nightly workflow 内の実行例:

```bash
RUNSET="$(cat artifacts/bench-ts-runset.txt)"
node scripts/quality/bench-compare.mjs \
  --baseline "${RUNSET}" \
  --candidate ts-self="${RUNSET}" \
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

- `ts-self` は自己比較のため、`p95 ratio <= 0.85` と `throughput ratio >= 1.20` の改善閾値を原理的に満たせず、`overall` は原則 `fail` になる。
- この `overall` は nightly monitor のアクション判定には使わない。monitor の対象は `reproducibility`（CV / checksum）と trend の証跡化である。
- 暫定運用では `compare-bench.mjs`（2点比較・5%許容）と `bench-compare`（report-only）を併用する。

#### 5.1.2 monitor 運用方針（compare-bench 併用と fail-on-threshold-breach 適用条件）
- 現行の report-only 運用:
  - 逸脱検知: `compare-bench.mjs`（<= 5%）を継続利用
  - 証跡化: `bench-compare` の JSON / Markdown を nightly artifact として保存
- `--fail-on-threshold-breach` 適用検討の前提条件:
  - 直近 14 日で `bench-runset`（2 run 以上）が欠損なく継続取得できる
  - `reproducibility`（`p95 CV`, `throughput CV`, `checksum`）が 7 日連続で安定し、ノイズ起因の fail が許容閾値内
  - 切替条件（on / off 条件、ロールバック手順）を運用手順に明記済み
- 上記を満たした時点で、`monitor` job 内の `bench-compare` を段階的に gate 化する。最初は warning-only、その後 fail-on-breach に移行する。

#### 5.1.3 Nightly 失敗時の artifact 確認手順
1. GitHub Actions の `Nightly Matrix` 実行履歴から失敗 run を開き、`monitor` job の `Upload artifacts` ステップが実行済みであることを確認する。
2. run の Artifacts から `nightly-artifacts` をダウンロードし、`artifacts/bench-ts-compare.json` を確認する。
   - `ok: false` または `rows[].pass: false` は、`compare-bench.mjs`（2点比較・5%許容）での閾値逸脱箇所を示す。
3. `artifacts/bench-ts-runset.txt` と `artifacts/bench-ts-run*.json` を参照し、比較対象 run の取り違えがないことを検証する。
4. `artifacts/bench-compare.json` / `artifacts/bench-compare.md` が存在する場合は、再現性（CV / checksum）と trend の補助情報として確認する。

#### 5.2 指標の一次データ源と算出方式（確定）
- 入力契約: `benchmark-report/v1`
  - schema: `schema/benchmark-report.schema.json`
- 判定 criteria 契約: `bench-criteria/v1`
  - default: `configs/bench-criteria.default.json`
  - schema: `schema/bench-criteria.schema.json`
- 指標マッピング:
  - `p95 latency` = `metrics.p95`
  - `error rate` = `metrics.errorRate`
  - `cold start` = `metrics.coldStartMs`
  - `peak RSS` = `metrics.peakRssMb`
  - `throughput` = `sum(summary[].hz)`（`summary` は non-empty、`hz > 0`）
- 比率計算: `ratio = candidate / baseline`
  - しきい値の向き: `p95` / `cold start` / `peak RSS` は上限、`throughput` は下限
  - baseline 値が `<= 0` の比率は `null`（non-applicable）として扱い、当該比率判定のみ fail 強制しない
- 再現性計算: `CV = stddev / mean`
  - `p95 CV`: 複数 run の `metrics.p95` から算出
  - `throughput CV`: 複数 run の `sum(summary[].hz)` から算出
  - run が 1 件のみの場合、CV は `null`（non-applicable）
- checksum 一致率: run 群の `benchmark-report/v1` から `schemaVersion + summary + metrics` を正規化（summary は name 順、JSON key 安定化）して `sha256` 比較し、先頭 run と一致した件数 / 全件数で算出
- error rate 上限: `max(0.5, baseline.errorRate + 0.2)`（percentage point）
- 比較成果物契約: `artifacts/bench-compare.json`
  - `schemaVersion: bench-compare/v1`
  - schema: `schema/bench-compare.schema.json`

### 6. #2409 チェックリスト対応

| #2409 first slice 項目 | 対応ドキュメント |
| --- | --- |
| 1) PoC成功基準の定義 | `docs/quality/poc-success-criteria-2409.md` |
| 2) 比較計測テンプレート追加 | `docs/templates/quality/poc-comparison-metrics-template.md` |
| 3) ADRテンプレート追加 | `docs/templates/quality/adr-poc-adoption-template.md` |
| 4) docs index の最小更新 | `docs/README.md`, `docs/templates/quality/README.md` |
