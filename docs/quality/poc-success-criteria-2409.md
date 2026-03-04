# PoC成功基準（#2409 first slice: TS baseline vs Go/Rust）

目的:
- TypeScript baseline と Go/Rust 候補を同一条件で比較し、採用/不採用を機械的に判定できる基準を定義する。

前提条件（2026-03-04時点）:
- Node.js: `>=20.11 <23`（`package.json` の `engines.node`）
- pnpm: `10.0.0`（`package.json` の `packageManager`）
- 比較対象: `TS baseline` / `Go candidate` / `Rust candidate`
- 同一入力データ・同一シナリオ・同一計測スクリプトで比較する。

## 1. 計測プロトコル

- シナリオ: `small` / `medium` / `large` の3段階（入力件数は比較テンプレートに固定値を記録）。
- 反復回数: 各実装・各シナリオでウォームアップ2回 + 本計測10回。
- 計測値: `throughput(req/s)`, `p95 latency(ms)`, `error rate(%)`, `peak RSS(MB)`, `cold start(ms)`。
- TS baseline の機械可読成果物は `artifacts/bench.json`（schema: `schema/benchmark-report.schema.json`）。主要指標キーは `metrics.p95` / `metrics.errorRate` / `metrics.coldStartMs` / `metrics.peakRssMb`。
- 集計方法: 中央値（median）を主指標、ばらつきは `CV = stddev / mean` で算出。
- ベースライン比: `ratio = candidate / ts_baseline`。
  - latency改善率（小さいほど良い）: `latency_improvement = (1 - ratio) * 100`
  - throughput改善率（大きいほど良い）: `throughput_improvement = (ratio - 1) * 100`

## 2. 成功基準（定量・判定可能）

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

## 3. Go / No-Go ルール

- **Go**: 必須基準を全て充足し、撤収条件（第4章）に該当しない。
- **Conditional Go**: 必須基準を充足しつつ、参考指標のみ未達。改善計画と期限（最大2スプリント）を ADR に明記する。
- **No-Go**: 必須基準を1つでも未達、または撤収条件に該当。

## 4. 撤収条件（早期中止・不採用）

以下のいずれかを満たした時点で当該候補は撤収（不採用）とする。

1. 2回連続計測で性能必須基準を2項目以上未達。
2. 再現性基準（CVまたはchecksum一致）を1回でも満たせない。
3. 実装工数が `20` 人日を超過見込み（残作業見積を含む）。
4. CI運用差分が `+25%` を超え、改善策の見込みがない。
5. 重大障害（P1相当）または Critical 脆弱性が解消不能。

## 5. 証跡（必須成果物）

- 比較計測結果: `docs/templates/quality/poc-comparison-metrics-template.md` を使用して記録。
- 判定記録: `docs/templates/quality/adr-poc-adoption-template.md` を使用して ADR 化。
- TS baseline 実行コマンド: `pnpm exec tsx src/cli.ts bench`
- TS baseline 出力: `artifacts/bench.json`（機械可読） / `artifacts/bench.md`（人間可読）
- 実行ログ: コマンド、使用コミットSHA、計測日時、実行環境（CPU/メモリ/OS/ランタイム）を必ず添付。

### 5.1 比較判定コマンド（bench.json -> 比率/合否）

`benchmark-report/v1`（`artifacts/bench.json`）を入力に、PoC比較の比率と必須閾値判定を機械的に生成する。

```bash
node scripts/quality/bench-compare.mjs \
  --baseline artifacts/bench-ts-run1.json,artifacts/bench-ts-run2.json \
  --candidate go=artifacts/bench-go-run1.json,artifacts/bench-go-run2.json \
  --candidate rust=artifacts/bench-rust-run1.json,artifacts/bench-rust-run2.json \
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

複数runを比較する場合は、run群を先に標準化してから `bench-compare` に渡す:

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
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

- 出力JSON: `artifacts/bench-compare.json`
- 出力Markdown: `artifacts/bench-compare.md`
- runset（baseline入力）: `artifacts/bench-ts-runset.txt`
- 必須判定: `p95 ratio <= 0.85`, `throughput ratio >= 1.20`, `error rate <= max(0.5, baseline + 0.2pt)`, `peak RSS ratio <= 1.15`
- 再現性判定: `p95 CV <= 0.05`, `throughput CV <= 0.05`（runCount >= 2 のとき）
- 出力整合判定: `checksum match rate == 100%`
- 参考判定: `cold start ratio <= 1.10`

### 5.2 指標の一次データ源と算出方式（確定）

- 入力契約: `benchmark-report/v1`（`schema/benchmark-report.schema.json`）
- 指標マッピング:
  - `p95 latency` = `metrics.p95`
  - `error rate` = `metrics.errorRate`
  - `cold start` = `metrics.coldStartMs`
  - `peak RSS` = `metrics.peakRssMb`
  - `throughput` = `sum(summary[].hz)`（`summary` は non-empty、`hz > 0`）
- 比率計算: `ratio = candidate / baseline`
  - しきい値の向き: p95/cold-start/peak-RSS は上限、throughput は下限
  - baseline 値が `<= 0` の比率は `null`（non-applicable）として扱い、当該比率判定のみ fail 強制しない
- 再現性計算: `CV = stddev / mean`
  - `p95 CV`: 複数runの `metrics.p95` から算出
  - `throughput CV`: 複数runの `sum(summary[].hz)` から算出
  - run が1件のみの場合、CVは `null`（non-applicable）
- checksum 一致率: run群の `benchmark-report/v1` から `schemaVersion + summary + metrics` を正規化（summaryはname順、JSON key安定化）して `sha256` 比較し、先頭runと一致した件数/全件数で算出
- error rate 上限: `max(0.5, baseline.errorRate + 0.2)`（percentage point）
- 比較成果物契約: `artifacts/bench-compare.json`（`schemaVersion: bench-compare/v1`、schema: `schema/bench-compare.schema.json`）

## 6. #2409 チェックリスト対応

| #2409 first slice 項目 | 対応ドキュメント |
| --- | --- |
| 1) PoC成功基準の定義 | `docs/quality/poc-success-criteria-2409.md` |
| 2) 比較計測テンプレート追加 | `docs/templates/quality/poc-comparison-metrics-template.md` |
| 3) ADRテンプレート追加 | `docs/templates/quality/adr-poc-adoption-template.md` |
| 4) docs index の最小更新 | `docs/README.md`, `docs/templates/quality/README.md` |
