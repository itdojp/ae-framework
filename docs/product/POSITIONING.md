# ae-framework の位置づけ（比較と導入指針）

> Language / 言語: English | 日本語

---

## English (Summary)

Clarifies how ae-framework differs from adjacent categories (CI templates, quality tools, spec/contract frameworks, agent runtimes) and provides adoption guidance.

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
- PR運用における **最小ゲート（verify-lite + Copilot Review Gate）** を標準化できる
- **opt-in（ラベル/Slash）** により重い検証を必要時のみ起動できる
- 成果物（summary/envelope）を通じて **監査性・説明責任** を担保できる

## 5. 導入パターン（判断ガイド）

### 5.1 既存CIはあるが運用が揺れている
→ **verify-lite + Copilot gate の最小導入** から開始  
（`docs/product/MINIMAL-ADOPTION.md` を参照）

### 5.2 仕様運用が未整備
→ AE-Spec / AE-IR を導入し、**仕様→検証の基線** を作る  
（`docs/product/USE-CASES.md` の「仕様運用」）

### 5.3 重い検証や形式検証を段階導入したい
→ opt-in ラベル/Slash による **段階的な検証強化** を選択  
（`docs/ci/OPT-IN-CONTROLS.md`）

### 5.4 エージェント活用を進めたい
→ CodeX/Claude Code の playbook による **成果物収集** を導入  
（`docs/codex/ae-playbook.md`）

## 6. 非対象（明確に提供しないもの）
- エージェントの実行ランタイムやIDEプラグイン
- ホスト型CI/CDサービス
- 汎用UIスターター

## 7. 参照
- `docs/product/OVERVIEW.md`
- `docs/product/MINIMAL-ADOPTION.md`
- `docs/ci/OPT-IN-CONTROLS.md`
