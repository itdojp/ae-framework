# 開発者向け入門ガイド

> 🌍 Language / 言語: 日本語 | English

---

## English (Overview)

Developer onboarding guide for ae-framework: NL → BDD → Formal → TDD → Code → Repair cycle using agents (e.g., CodeX/Claude Code). Explains the three pillars (BDD, Formal Methods, TDD), architecture flow, and core components. See Japanese sections for detailed steps and examples.

## 1. システムの目的
ae-framework は **自然言語の要求から、曖昧さのない厳密仕様とテストを経て、正しく動作するコードを自動生成する** ことを目的としています。
原理は次の 3 本柱で構成されています。

- **BDD (Behavior Driven Development)**
  利用者視点のシナリオ（Given-When-Then）で振る舞いを定義。
- **形式的手法 (Formal Methods)**
  TLA+/Alloy/契約記述などで数学的に仕様を検証。
- **TDD (Test Driven Development)**
  生成されたテストを起点にコードを実装し、常にグリーンになることを保証。

この 3 つを AI エージェント（CodeX CLI など）と組み合わせて **要求 → 仕様 → 実装 → 修復** の一筆書きサイクルを実現します。

---

## 2. アーキテクチャ概要

```
自然言語要求
   ↓ (TestGenerationAgent)
   BDDシナリオ (.feature)
   ↓ (FormalAgent)
   形式仕様 (TLA+ / Alloy / 契約)
   ↓ (モデルチェック / verify:lite / verify:formal)
   テストコード生成
   ↓ (CodeGenerationAgent)
   実装コード
   ↓ (ae-fix, CEGIS)
   自動修復・再検証
```

### 主なコンポーネント
- **TestGenerationAgent**
  NL 要求から BDD シナリオを生成。
- **FormalAgent**
  BDD を入力に形式仕様 (TLA+, Alloy, state machines) を生成。
- **CodeGenerationAgent**
  テスト駆動で API や実装コードを生成。
- **verify workflows / formal runners**
  CI の required check 名は `verify-lite`、ローカルの実行入口は `pnpm run verify:lite`、formal runners の更新は `pnpm run verify:formal` を使います。
- **ae-fix (CEGIS)**
  失敗アーティファクトをもとに自動修復を試行。

---

## 3. 開発者が理解すべき原理

### (1) BDD → 形式仕様
- **Given-When-Then** を AE-IR という中間表現に変換し、TLA+/Alloy のテンプレートに落とす。
- モデルチェックで不変量や安全性を保証。

### (2) 形式仕様 → テスト/コード
- 形式仕様で定義された制約から **TDD テスト**が生成される。
- 実装コードは常にテストが前にあり、RED-GREEN サイクルを維持。

### (3) トレーサビリティ
- **traceId** を基軸に、
  - .feature のシナリオ
  - TLA+/Alloy のプロパティ
  - Vitest テスト
  - 実装ファイル
  を 1 本の線で結び、PR 上でカバー率を可視化。

### (4) 自動修復（CEGIS）
- 失敗したテストや形式検証の反例を入力に、AI が修正案を提示。
- 開発者は Dry-run / 信頼度閾値で制御できる。

---

## 4. 実際の開発フロー

1. **要求を追加**
   `spec/bdd/features/*.feature` に新しいシナリオを記述（または生成）。
2. **形式仕様と契約を検証**
   `pnpm run spec:lint` / `pnpm run spec:compile` / `pnpm run spec:validate` で仕様を整え、必要に応じて `pnpm run verify:formal` で formal runners を実行します。
   日常 PR の baseline は `verify-lite` / `policy-gate` / `gate` です。
3. **テストと実装を更新**
   current repo では単一の `ae:generate` は提供されません。対象 slice の spec / test / implementation を更新し、`pnpm test` で回帰を確認します。
4. **CI で検証**
   - formal aggregate → `artifacts/hermetic-reports/formal/summary.json`
   - normalized formal summaries → `artifacts/formal/formal-summary-v1.json`, `artifacts/formal/formal-summary-v2.json`
   - report envelope / trace summary → `artifacts/report-envelope.json`, `artifacts/trace/report-envelope.json`
5. **失敗時は修復**
   `ae-framework fix apply --input failures.json --output .ae/auto-fix --dry-run` で修復候補を確認し、必要なら `--verify --verify-profile lite` を付けて再検証します。

---

## 5. 環境とコマンド

### 必須環境
- Node.js 20+
- Docker/Podman
- Java (TLA+ 用)
- Alloy Analyzer

### よく使うコマンド
- `pnpm run spec:lint` – spec lint
- `pnpm run spec:compile` – spec compile
- `pnpm run spec:validate` – spec validate
- `pnpm run verify:lite` – current PR baseline 相当のローカル検証
- `pnpm run verify:formal` – formal runners と aggregate summary の更新
- `pnpm test` – Vitest 実行
- `ae-framework fix apply --input failures.json --output .ae/auto-fix --dry-run` – failure artifact から修復候補を確認

---

## 6. 参考リソース
- [docs/phases/*] – 各フェーズの詳細説明
- [docs/architecture/*] – 全体アーキテクチャ図
- [docs/integrations/*] – 外部ツールとの連携方法
- `examples/inventory/` – 在庫予約ドメインのデモシナリオ

---

## 7. 今後の展望
- Proof assistant（Coq/Dafny）との統合（オプション）
- 非機能ゲート（性能・a11y・互換性）の標準化
- PR コメントでの自動サマリと反例可視化
