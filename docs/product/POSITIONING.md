---
docRole: narrative
lastVerified: '2026-03-22'
---
# ae-framework の位置づけ（比較と導入指針）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
This document supports adoption decisions by clarifying how `ae-framework` differs from adjacent categories and by outlining practical adoption patterns.

### 2. Decision Axes
| Axis | Meaning |
| --- | --- |
| Purpose | What problem the mechanism is intended to solve |
| Operating scope | Whether it covers specs, tests, CI, artifacts, and operations |
| Auditability | Whether change rationale and verification outputs remain traceable |
| Reproducibility | Whether the same result can be re-executed deterministically |
| Cost | Adoption, operation, and learning cost |
| Extensibility | Whether heavier checks can be enabled incrementally |

### 3. Comparison with Adjacent Categories
#### 3.1 CI template collections
- Similarity: both standardize CI execution
- Difference: `ae-framework` also standardizes artifacts, evidence, and gate operation

#### 3.2 Quality-gate tools
- Similarity: both make pass/fail judgments from quality signals
- Difference: `ae-framework` assumes composed operation of lightweight and heavyweight gates instead of a single tool verdict

#### 3.3 Spec / contract test frameworks
- Similarity: both validate behavior against specifications
- Difference: `ae-framework` integrates specification, tests, CI gates, and generated evidence into one operating model

#### 3.4 Agent runtimes
- Similarity: both assume agent-assisted delivery
- Difference: `ae-framework` is not the runtime. It is the operating surface that receives artifacts, verification outputs, and policy decisions

### 4. Practical Strengths
- Standardized minimum PR baseline on `main`: `verify-lite`, `policy-gate`, and `gate`
- Opt-in heavy verification through labels or slash commands when needed
- Artifact-driven accountability through summaries, envelopes, and quality decision records

### 5. Adoption Patterns
#### 5.1 Existing CI exists, but operation is inconsistent
Start from the minimum PR baseline: `verify-lite` + `policy-gate` + `gate`.

#### 5.2 Specification operation is not yet in place
Introduce AE-Spec / AE-IR first so that specification-to-verification becomes explicit.

#### 5.3 Heavy checks or formal verification should be phased in gradually
Use opt-in labels / slash commands and add heavy verification incrementally.

#### 5.4 Agent usage needs stronger operational control
Introduce Codex / Claude Code playbooks together with artifact collection and review evidence.

### 6. Non-goals
- Agent runtimes or IDE plugins
- Hosted CI/CD services
- Generic UI starter kits

### 7. References
- `docs/product/OVERVIEW.md`
- `docs/quality/adoption-sample-flow.md`
- `docs/ci/label-gating.md`

---

## 日本語

## 1. 目的
ae-framework の導入判断を支援するため、**類似カテゴリとの棲み分け**と**導入パターン**を整理します。

## 2. 比較軸（判断基準）

| 比較軸 | 説明 |
| --- | --- |
| 目的 | 何を解決するための仕組みか |
| 運用範囲 | 仕様/テスト/CI/成果物/運用までを含むか |
| 監査性 | 変更理由や検証結果が追跡可能か |
| 再現性 | 同じ結果を再実行できるか |
| コスト | 導入/運用/学習コスト |
| 拡張性 | opt-in で重い検証を追加できるか |

## 3. 類似カテゴリとの比較（概念）

### 3.1 CIテンプレ集（Workflow雛形）
- **共通点**: CIを標準化する
- **差分**: ae-framework は「成果物（artifacts/reports）と品質ゲートの運用」まで含める

### 3.2 品質ゲートツール（SAST/依存監査/カバレッジ等）
- **共通点**: 品質メトリクスに基づく合否判定
- **差分**: ae-framework は **複数ゲートの合成運用（軽量/重いの分離）** を前提とする

### 3.3 仕様/契約テスト基盤
- **共通点**: 仕様に基づく検証
- **差分**: ae-framework は **仕様→テスト→CIゲート→成果物** を一体で運用する

### 3.4 エージェント実行ランタイム
- **共通点**: エージェント活用を前提とする
- **差分**: ae-framework は **実行ランタイムではなく、成果物と検証の受け皿** を提供する

## 4. ae-framework の優位性（要約）
- PR運用における **最小ゲート（`verify-lite` + `policy-gate` + `gate`（Copilot Review Gate））** を標準化できる
- **opt-in（ラベル/Slash）** により重い検証を必要時のみ起動できる
- 成果物（summary/envelope）を通じて **監査性・説明責任** を担保できる

## 5. 導入パターン（判断ガイド）

### 5.1 既存CIはあるが運用が揺れている
→ **`verify-lite` + `policy-gate` + `gate` の最小導入** から開始
（`docs/quality/adoption-sample-flow.md` を参照）

### 5.2 仕様運用が未整備
→ AE-Spec / AE-IR を導入し、**仕様→検証の基線** を作る  
（`docs/product/OVERVIEW.md` の「仕様運用・ユースケース」）

### 5.3 重い検証や形式検証を段階導入したい
→ opt-in ラベル/Slash による **段階的な検証強化** を選択  
（`docs/ci/label-gating.md`）

### 5.4 エージェント活用を進めたい
→ CodeX/Claude Code の playbook による **成果物収集** を導入  
（`docs/codex/ae-playbook.md`）

## 6. 非対象（明確に提供しないもの）
- エージェントの実行ランタイムやIDEプラグイン
- ホスト型CI/CDサービス
- 汎用UIスターター

## 7. 参照
- `docs/product/OVERVIEW.md`
- `docs/quality/adoption-sample-flow.md`
- `docs/ci/label-gating.md`
