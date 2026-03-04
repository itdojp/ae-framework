# PoC比較計測テンプレート（TS baseline vs Go/Rust）

用途:
- `docs/quality/poc-success-criteria-2409.md` の成功基準に沿って、同一条件の比較計測結果を記録する。

## 0. メタデータ

| 項目 | 値 |
| --- | --- |
| Issue / Slice | #2409 / first slice |
| 実施日 | YYYY-MM-DD |
| 実施者 | @owner |
| 判定対象 | TS baseline / Go candidate / Rust candidate |
| Repository commit SHA | `<sha>` |
| Node.js | `vXX.XX.X` |
| pnpm | `X.X.X` |
| Go | `goX.XX.X` |
| Rust | `rustc X.XX.X` |
| OS / CPU / Memory | `<example: Ubuntu 24.04 / 8 vCPU / 16GB>` |

## 1. 入力条件（固定化）

| シナリオ | 入力規模 | 同時実行数 | 反復 | 備考 |
| --- | --- | --- | --- | --- |
| small | `<n>` | `<c>` | warmup 2 + measure 10 |  |
| medium | `<n>` | `<c>` | warmup 2 + measure 10 |  |
| large | `<n>` | `<c>` | warmup 2 + measure 10 |  |

## 2. 性能比較

`ratio = candidate / ts_baseline`（latency, rss, cold start）  
`ratio = candidate / ts_baseline`（throughput は 1.0 超が改善）

### 2.1 small

| 指標 | TS baseline | Go candidate | Go ratio | Rust candidate | Rust ratio | Pass/Fail |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| throughput (req/s) |  |  |  |  |  |  |
| p95 latency (ms) |  |  |  |  |  |  |
| error rate (%) |  |  |  |  |  |  |
| peak RSS (MB) |  |  |  |  |  |  |
| cold start (ms) |  |  |  |  |  |  |

### 2.2 medium

| 指標 | TS baseline | Go candidate | Go ratio | Rust candidate | Rust ratio | Pass/Fail |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| throughput (req/s) |  |  |  |  |  |  |
| p95 latency (ms) |  |  |  |  |  |  |
| error rate (%) |  |  |  |  |  |  |
| peak RSS (MB) |  |  |  |  |  |  |
| cold start (ms) |  |  |  |  |  |  |

### 2.3 large

| 指標 | TS baseline | Go candidate | Go ratio | Rust candidate | Rust ratio | Pass/Fail |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| throughput (req/s) |  |  |  |  |  |  |
| p95 latency (ms) |  |  |  |  |  |  |
| error rate (%) |  |  |  |  |  |  |
| peak RSS (MB) |  |  |  |  |  |  |
| cold start (ms) |  |  |  |  |  |  |

## 3. 再現性

| 指標 | TS baseline | Go candidate | Rust candidate | Pass/Fail |
| --- | ---: | ---: | ---: | --- |
| CV(throughput) |  |  |  |  |
| CV(p95 latency) |  |  |  |  |
| checksum 一致率 (%) |  |  |  |  |
| 再現コマンド成功率 (%) |  |  |  |  |

## 4. 実装コスト

| 項目 | TS baseline | Go candidate | Rust candidate | 備考 |
| --- | ---: | ---: | ---: | --- |
| 設計工数（人日） |  |  |  |  |
| 実装工数（人日） |  |  |  |  |
| テスト/検証工数（人日） |  |  |  |  |
| 文書化工数（人日） |  |  |  |  |
| 合計工数（人日） |  |  |  |  |
| 新規メンバー再現時間（分） |  |  |  |  |

## 5. 運用差分

| 項目 | TS baseline | Go candidate | Rust candidate | Pass/Fail |
| --- | ---: | ---: | ---: | --- |
| CI実行時間（分） |  |  |  |  |
| CI増分（%） |  |  |  |  |
| 監視項目欠落数 |  |  |  |  |
| 新規 Critical 脆弱性数 |  |  |  |  |
| 追加運用Runbook数 |  |  |  |  |

## 6. 総合判定

| 候補 | 性能 | 再現性 | 実装コスト | 運用差分 | 撤収条件 | 判定 |
| --- | --- | --- | --- | --- | --- | --- |
| Go candidate | Pass/Fail | Pass/Fail | Pass/Fail | Pass/Fail | 該当/非該当 | Go / Conditional Go / No-Go |
| Rust candidate | Pass/Fail | Pass/Fail | Pass/Fail | Pass/Fail | 該当/非該当 | Go / Conditional Go / No-Go |

## 7. 実行コマンドと証跡リンク

```text
# TS baseline（機械可読: artifacts/bench.json）
pnpm exec tsx src/cli.ts bench

# TS baseline の主要指標抽出例
jq '.metrics | {p95, errorRate, coldStartMs, peakRssMb}' artifacts/bench.json

# Go / Rust candidate（同一シナリオ・同一入力で実行）
<go-benchmark-command>
<rust-benchmark-command>

# 比較判定（bench.json -> 比率/合否）
node scripts/quality/bench-compare.mjs \
  --baseline artifacts/bench-ts.json \
  --candidate go=artifacts/bench-go.json \
  --candidate rust=artifacts/bench-rust.json \
  --out-json artifacts/bench-compare.json \
  --out-md artifacts/bench-compare.md
```

- TS baseline raw result: `artifacts/bench.json`（schema: `schema/benchmark-report.schema.json`）
- TS baseline summarized report: `artifacts/bench.md`
- candidate raw result: `<path/to/bench-go-or-rust-results>`
- comparison json: `artifacts/bench-compare.json`
- comparison markdown: `artifacts/bench-compare.md`
- logs: `<path/to/logs>`
- related ADR: `<path/to/adr>`
