# TLA+ を全面活用する ae-framework 構成案

## 全体アーキテクチャ

- **唯一の正**: TLA+ 仕様（抽象 → 準抽象 → 実装近傍）
- **両輪**: 形式検証（TLC / Apalache / TLAPS）＋ 実動検証（trace validation / model-based test）
- **生成**: TLA+ から BDD/テスト・OpenAPI/スキーマ・状態モニタを半自動生成
- **連携**: `verify:conformance` は TLA+ の **モデル→テスト** と **実装→トレース→仕様** の両方向で接続
- **ゲーティング**: 仕様→実装の整合性を CI の「必須ゲート」に昇格

---

## リポジトリ構成案

```
ae-framework/
├─ specs/
│  ├─ formal/
│  │  ├─ 00_core/                    # 共通モジュール
│  │  ├─ 10_abstract/                # 抽象仕様
│  │  ├─ 20_refined/                 # 準抽象
│  │  ├─ 30_impl/                    # 実装近傍
│  │  ├─ mappings/                   # Refinement Mapping
│  │  └─ configs/                    # TLC/Apalache cfg
│  └─ pluscal/                       # PlusCal
│
├─ tools/
│  ├─ tla/                           # tla2tools, apalache, tlaps
│  ├─ generators/                    # BDD/OpenAPI/Monitors 生成
│  ├─ trace/                         # トレース schema/projectors/validators
│  └─ ci/                            # CI 用スクリプト
│
├─ adapters/                         # TS/Go/Py 用 SDK/モニタ
├─ apps/                             # 実装
├─ tests/                            # bdd, model-based, conformance
└─ docs/                             # ドキュメント
```

---

## パイプライン

### 1) 仕様作成と精緻化
- `10_abstract`: 不変条件と活性を定義
- `20_refined`: 非同期・故障・重試行を追加
- `30_impl`: API/DB/並行制御を導入
- `mappings`: 抽象↔実装の対応を明示

### 2) 仕様から成果物を生成
- **BDD 生成**: TLA+ Action → Given/When/Then
- **OpenAPI 生成**: State/Action 入出力 → API 契約
- **モニタ生成**: 不変条件 → 実装言語のアサーション

### 3) 実装側のトレース
- 共通トレーススキーマ（NDJSON/OTLP）
- Projector でログを仕様変数に射影
- Validator で TLC/Apalache による妥当性確認

### 4) CI/CD のゲート
- **Spec Check**: 仕様の安全性/活性検証
- **Generate**: 成果物の自動生成と差分チェック
- **Model-Based Test**: 状態遷移網羅度を測定
- **Conformance**: 実装トレースの妥当性検証

---

## GitHub Actions サンプル

```yaml
name: spec-driven-pipeline

on:
  push:
    branches: [ main ]
  pull_request:

jobs:
  spec-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Setup TLA+ / Apalache
        run: tools/ci/setup-tla.sh
      - name: TLC
        run: tools/ci/run-tlc.sh specs/formal
      - name: Apalache
        run: tools/ci/run-apalache.sh specs/formal

  generate-artifacts:
    needs: spec-check
    runs-on: ubuntu-latest
    steps:
      - run: tools/generators/bdd-from-tla/run.sh
      - run: tools/generators/openapi-from-tla/run.sh
      - run: tools/generators/monitors-from-tla/run.sh
      - run: git diff --exit-code || exit 1

  model-based-tests:
    needs: generate-artifacts
    runs-on: ubuntu-latest
    steps:
      - run: tools/ci/run-model-based-tests.sh

  conformance:
    needs: model-based-tests
    runs-on: ubuntu-latest
    steps:
      - run: tools/ci/run-e2e-with-tracing.sh
      - run: tools/trace/projectors/project.sh traces/*.ndjson > traces/projected.ndjson
      - run: tools/trace/validators/validate.sh traces/projected.ndjson specs/formal/30_impl
```

---

## verify:conformance との統合
- **モデル→テスト**: TLA+ から生成した BDD/テストを `verify:conformance` で実行
- **実装→仕様**: 実行ログを NDJSON で吐き、Trace Validator に投入
- **レポート統合**: 遷移網羅率・不変条件・E2E 成否を同一ダッシュボードに集約

---

## 設計ルール
1. **仕様先行**: TLA+ 変更を PR で行い、生成物と実装が追随
2. **Refinement Mapping の明示**: JSON/TLA で管理
3. **探索境界を宣言**: cfg に明記
4. **命名統一**: 仕様変数名と BDD/API/イベント名を射影可能に
5. **トレース義務化**: 実行経路に対応する仕様イベントを必ず記録

---

## ミニサンプル

`specs/formal/10_abstract/KvOnce.tla`
```tla
--------------------------- MODULE KvOnce ---------------------------
EXTENDS Naturals, Sequences

CONSTANT Keys, Values
VARIABLES store

Init == store = [k \in Keys |-> [written |-> FALSE, val |-> NULL]]

Put(k, v) ==
  /\ k \in Keys /\ v \in Values
  /\ ~store[k].written
  /\ store' = [store EXCEPT ![k] = [written |-> TRUE, val |-> v]]

NoOverwrite == \A k \in Keys: store[k].written => UNCHANGED store[k].val

Next == \E k \in Keys, v \in Values: Put(k, v)

Spec == Init /\ [][Next]_store

THEOREM Safety == Spec => []NoOverwrite
====================================================================
```

`specs/formal/mappings/KvOnce.impl.json`
```json
{
  "stateMap": {
    "store[k].written": "db.objects[k] != null",
    "store[k].val": "db.objects[k].contentHash"
  },
  "actionMap": {
    "Put(k,v)": "POST /objects {key:k, body:v}"
  }
}
```

---

## 導入ステップ
1. **最小ドメイン選定**（例: KV-once）
2. **CI ゲート化**（spec-check / generate / conformance）
3. **モデル→テスト自動化**（BDD 生成を標準化）
4. **サービス拡張ごとに Refinement 階層を追加**
5. **ダッシュボード整備**（網羅率・不整合・回帰影響を可視化）


## 現状進捗（2025-10-04）

### 完了
- KvOnce 抽象/準抽象/実装仕様と Refinement Mapping を追加（PR #1020）
- TLC/Apalache 用 cfg と `pnpm run spec:kv-once:tlc` / `spec:kv-once:apalache` スクリプトを整備し、ツール未導入時は graceful skip
- `.github/workflows/spec-check.yml` を整備し、KvOnce を CI でチェック（ツール未導入環境でもスキップ扱い）
- `docs/TLA+/kv-once-poc.md` に PoC の背景と実行方法をまとめた

### 継続中
- 自動生成ワークフロー（BDD/OpenAPI/モニタ）の差分チェック
- Trace Validator / Projector の実装と `verify:conformance` への統合
- formal-summary を PR コメントへ自動投稿
- generate-artifacts / model-based-tests の最小ゲート `.github/workflows/spec-generate-model.yml` を運用し、対象を段階的に拡充
- KvOnce のトレース検証 (`scripts/trace/mock-otlp-service.mjs` → `scripts/trace/convert-otlp-kvonce.mjs` → `scripts/trace/run-kvonce-conformance.sh`) を CI に組み込み、サンプル OTLP ログの収集 / 変換を自動化

### 実行ヒント

```bash
# KvOnce 抽象仕様を TLC で検証（非破壊）
pnpm run spec:kv-once:tlc

# Apalache 版（インストール済みの場合）
pnpm run spec:kv-once:apalache

# トレース検証（OTLP → NDJSON → Projection → Validation）
node scripts/trace/mock-otlp-service.mjs
bash scripts/trace/run-kvonce-conformance.sh --format otlp --input hermetic-reports/trace/collected-kvonce-otlp.json
```

- 駆動結果は `hermetic-reports/formal/tla-summary.json` に出力される。
- CI 取り込み時はラベル `run-formal` などで opt-in しつつ、成功時に summary を PR コメントへ反映させる予定。

次ステップ：Spec Check の結果を Issue #1011 に紐付ける自動コメント、及び generate-artifacts/model-based-tests/conformance の追加。

### 省略予定 (Phase C)
- Projector / Validator を本運用に載せる前に必要なトレーススキーマ詳細設計（Issue #1011 ステップ3へ委譲）
- 自動生成 BDD/contract テスト全体の差分チェックと整合性検証（今後の generate-artifacts 拡張で対応）
- conformance ジョブにおける OTLP 収集とダッシュボード可視化（Issue #1011 ステップ5にて計画）
