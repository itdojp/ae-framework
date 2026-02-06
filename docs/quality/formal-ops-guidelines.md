# Formal Verification Ops Guidelines

フォーマル検証を運用する際の **推奨パターン / 命名 / 証跡 / CI 分割** を整理したガイドです。

## 1. 推奨運用パターン（TLC / Apalache / SMT / Alloy）

| ツール | 得意領域 | 推奨用途 |
| --- | --- | --- |
| TLC (TLA+) | 小さな状態空間の網羅探索 | 縮約モデルでの高速フィードバック |
| Apalache (TLA+) | 大きめの整数範囲 / BMC + 逐次改善 | 大数・前提付きモデルの検査 |
| SMT (Z3 / cvc5) | 数式系制約の検証 | パス条件や不変条件の局所検証 |
| Alloy | 構造・関係モデル | Small scope での構造整合性 |

**基本方針**
- TLC は「縮約モデル」で高速に回し、境界条件や反例探索を早く回収する。
- Apalache/SMT は「大数・前提付きモデル」で広い範囲を扱う。
- 同じモデル名でも前提・縮約が違う場合は **明示的に注記** する（誤解防止）。

## 2. 命名規約（ツール共通 vs ツール専用）

**共通仕様（tool-agnostic）**
- `spec/tla/DomainSpec.tla`（共通）
- `spec/tla/DomainSpec.cfg`（TLC 用）

**ツール専用（tool-specific）**
- `spec/tla/DomainSpec_apalache.tla`
- `spec/tla/DomainSpec_apalache.cfg`

**推奨注記**
- `spec/tla/README.md` に以下を記載:
  - モデル意図（`reduced` / `full`）
  - 主要な前提（整数範囲、対称性、抽象化）
- 成果物ディレクトリ名は **UTC を推奨**。ローカル表記を使う場合は `timezoneOffset` を併記し、`metadata` と整合させる。

## 3. Apalache テンプレ（stuttering / Next / deadlock）

### 最小テンプレ
```tla
VARIABLES vars

Init == ... \* 初期条件

Action1 == ... 
Action2 == ...

Stutter == UNCHANGED vars

Next == Action1 \/ Action2 \/ Stutter

Spec == Init /\ [][Next]_vars
```

### Deadlock 方針（推奨）
- **deadlock を禁止**したい場合:
  - `Stutter` を無条件に入れない（またはガード付きにする）。
  - `apalache-mc check --no-deadlock` を利用する。
- **stuttering を許容**する場合:
  - `StutterEnabled` のような **ガード条件**を用意し、意図的な停止と区別する。

## 4. 証跡のスケーリング（Git vs 外部）

**Git に残すべき最小セット**
- `summary.json`（要約）
- 重要ログの短い抜粋（エラー断片）
- 反例の **最小セット**（再現に必要な範囲のみ）

**外部（CI artifacts / ストレージ）に出すべきもの**
- 詳細ログ全文
- 大きな反例 JSON
- 大量のトレース / サンプル

**ローテーション指針**
- CI artifacts は **直近 N 回 / 30 日**を基準に保持。
- 重大インシデントは永続化し、`summary.json` から参照リンクを明示。

## 5. CI 分割テンプレ（verify-lite / verify-formal）

**verify-lite（必須）**: PR 毎に安定して実行する最小ゲート。

**verify-formal（任意 / 夜間）**: 時間・依存が重い検証はラベルやスケジュールで実行。

```yaml
# .github/workflows/verify-lite.yml
on:
  pull_request:
jobs:
  verify-lite:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - run: pnpm run verify:lite
```

```yaml
# .github/workflows/formal-verify.yml
on:
  workflow_dispatch:
  schedule:
    - cron: "0 2 * * *"  # optional nightly
  pull_request:
    types: [labeled]

jobs:
  formal:
    if: contains(github.event.pull_request.labels.*.name, 'run-formal')
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile
      - run: pnpm run verify:formal
```

補足:
- `enforce-formal` ラベルで Apalache の `ran/ok` をゲート化する運用が可能。
- 詳細な実行方法は `docs/quality/formal-runbook.md` を参照。
