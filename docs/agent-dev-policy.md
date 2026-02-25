# AIエージェント開発フロー基本方針（ae-framework / GitHub）

## 目的
本ドキュメントは、ae-framework を前提にした GitHub 開発フローの基本方針を定義し、
「どの工程を自動化し、どの監査点（合意・再現性・説明責任）を残すか」を明確化する。

## 適用範囲
- 対象リポジトリ：<repo名>
- 対象ブランチ：`main`（または `master` / `release/*`）
- 対象変更：コード、設定、IaC、ドキュメントを含む全変更

## 用語
- **PR**：監査ログの単位。議論・検証結果・承認・履歴を残すための最小単位。
- **Required checks**：Branch protection で必須化されたステータスチェック（例：PR verify / verify-lite）。
- **Low risk PR**：低リスク変更（人間Approve必須にしない）。
- **High risk PR**：中〜高リスク変更（人間Approve必須＋追加ゲート必須）。
- **Label gating**：PRラベルにより追加ゲート（重い検証、セキュリティ、厳格な契約検証等）を起動する運用。
- **CIサマリ**：CIが出力する要約（artifacts/サマリコメント等）。レビューの主要資料。
- **Codexレビュー**：PR上でのAIレビュー。最終保証ではなく補助シグナル。

---

## 基本方針（結論）
1. **ae-framework は GitHub Actions（PR verify / verify-lite 等）前提のため、原則 PR 単位で実行する。**
   - PRは required checks のゲートとして運用する。
   - `main` への直接 push は原則禁止（例外は「例外運用」参照）。

2. **低リスクPRは、人間のApproveを必須にしない。**
   - required checks が全て Green であれば **auto-merge** により完了とする。
   - ただし組織/チームのガバナンス要件により例外設定する場合がある。

3. **高リスクPRは、人間のApprove必須 + ラベルで追加ゲート起動とする。**
   - 何をレビューするかは、以下で明示する：
     - CIサマリ（検証結果の要約）
     - PRラベル（追加ゲートの宣言）
     - （必要に応じて）Codexレビューガイドライン（AGENTS.md 等）

---

## リスク分類ルール（Low / High）
### 原則
- **迷ったら High risk**（安全側）。
- 「対象領域」「影響範囲」「ロールバック容易性」で判定する。

### Low risk の例（Approve不要運用の候補）
- 影響が局所的で、変更範囲が限定的
- 外部I/F（API、スキーマ、ジョブI/F、帳票等）の変更なし
- 依存関係の追加/更新なし（または影響が極小で明確）
- 認証認可、暗号、会計/請求、データ移行、権限設定に関与しない
- 既存の自動テストで回帰が十分に捕捉できる
- ロールバックが容易（feature flag / revert で戻せる）

### High risk の例（Approve必須＋追加ゲート必須）
- 外部I/F変更（API仕様、DBスキーマ、イベント、ファイルI/F）
- 認証認可、権限、暗号、監査ログ、個人情報
- 依存関係の追加・大幅更新
- データ移行、会計・請求・在庫等のドメイン中核
- 境界/レイヤ/依存方向の変更（設計変更）
- 大規模リファクタ（差分が大きい、影響が読みづらい）
- テスト不十分、またはテスト追加が困難な領域

---

## PR運用ルール

### 1) PRは必ず作る（全件）
- **全ての変更はPRとして残す。**
- 「人間レビュー不要」=「PRが不要」ではない。
  - PRは監査ログの単位として残す（後追い調査/説明責任/再現性のため）。

### 2) Required checks（最低保証）
- `main` へのマージ条件として、以下を required checks に設定する：
  - `PR verify` または `verify-lite`（チーム標準）
  - （必要に応じて）doctest / lint / typecheck 等の軽量チェック
- required checks は **軽量・決定的**なものを基本とする。
  - 重い/不安定な検証は label gating で opt-in に寄せる（下記）。

### 3) Auto-merge（低リスク）
- Low risk と判定したPRは以下を満たす場合、auto-merge を許可する：
  - required checks が全て Green
  - PR本文にリスク分類（Low）とロールバック方法が記載されている
  - （任意）Codexレビューが付与されている、または「不要」理由が明記されている

### 4) 人間Approve必須（高リスク）
- High risk と判定したPRは以下を必須とする：
  - required checks が全て Green
  - **人間Approveが最低1名**
  - ラベルにより必要な追加ゲートを起動し、結果が Green
  - PR本文に「レビュー観点」「リスク」「ロールバック」が明記されている

---

## Label gating（追加ゲートの標準）
High risk PR は、PRラベルで追加ゲートを宣言する。

### 代表ラベル（例）
> 実際のラベル名はリポジトリの運用に合わせて調整する。

- `run-security`：SCA/SBOM/脆弱性スキャン等を実行（依存追加/更新、セキュリティ領域）
- `run-ci-extended`：統合テスト/重い回帰/長時間テスト等を実行
- `run-mutation` / `run-property` / `run-mbt`：必要時のみ（テスト強度の追加）
- `enforce-artifacts`：成果物（サマリ/仕様/JSON等）検証を厳格化（スキーマ検証など）
- `enforce-context-pack`：設計/契約（Context Pack等）検証を厳格化（境界/依存の監視など）
- `enforce-coverage` / `coverage:NN`：カバレッジ目標の強制

### ラベル付与ルール（例）
- 依存追加/更新 → `run-security`
- 外部I/F変更 → `run-ci-extended` + `enforce-artifacts`
- 境界/依存方向の変更 → `enforce-context-pack`
- データ移行/会計等の中核 → `run-ci-extended` + `run-security`（必要に応じて）
- リリース前ゲート → `run-ci-extended`（＋必要な強化ラベル）

---

## レビュー観点（「何を見るか」を固定する）
### Low risk（人間Approve不要時の確認観点）
- リスク分類がLowで妥当か（誤分類の検知）
- required checks が Green
- CIサマリの重大警告なし
- ロールバック記載がある

### High risk（人間Approve必須時の確認観点）
- リスク分類がHighで妥当か／追加ゲートが不足していないか
- CIサマリに基づき、受入基準が満たされているか
- 追加ゲート（label gating）の結果が Green
- 影響範囲（I/F、データ、権限、依存）の説明が十分か
- ロールバック/フェイルセーフ（段階リリース、feature flag 等）があるか

---

## Codexレビュー運用（任意だが推奨）
- PRには必要に応じて Codexレビューを付与する（例：`@codex review`）。
- Codexレビューは **最終保証ではなく補助シグナル**として扱う。
- レビュー観点は `AGENTS.md` 等に定義する（例：セキュリティ・PII・認可・ログ規約・API互換など）。

---

## 例外運用（緊急対応など）
- 原則として緊急時もPRは作成する（最短でDraft→即時マージ等は可）。
- 例外で direct push を許可する場合は、事後に必ずPRで差分と理由を記録する（監査性確保）。

---

## 変更履歴
- 2026/02/26 初版
