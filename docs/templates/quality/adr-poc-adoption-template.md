---
docRole: ssot
lastVerified: '2026-03-12'
owner: templates-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# ADRテンプレート（PoC採用/不採用判定）

## 1. メタ情報

- ADR ID: `ADR-XXXX`
- タイトル: `<短い判定名>`
- 日付: `YYYY-MM-DD`
- ステータス: `Proposed | Accepted | Rejected | Superseded`
- 対象Issue: `#2409`（必要に応じて派生Issueを追記）
- 関連ドキュメント:
  - `docs/quality/poc-success-criteria-2409.md`
  - `docs/templates/quality/poc-comparison-metrics-template.md`
  - `<計測結果ファイルへのリンク>`

## 2. 背景と課題

- 現状（TS baseline）の課題:
- PoCで検証したい論点:
- 本ADRで決定する範囲（in scope）:
- 本ADRで決定しない範囲（out of scope）:

## 3. 選択肢

| 選択肢 | 概要 | メリット | デメリット | 想定運用影響 |
| --- | --- | --- | --- | --- |
| A | TS継続（現行維持） |  |  |  |
| B | Go採用 |  |  |  |
| C | Rust採用 |  |  |  |
| D | 見送り（追加検証） |  |  |  |

## 4. 証跡サマリー（定量）

`docs/templates/quality/poc-comparison-metrics-template.md` の結果を要約する。

| 評価軸 | TS baseline | Go candidate | Rust candidate | 判定ルール | 結果 |
| --- | ---: | ---: | ---: | --- | --- |
| 性能 |  |  |  | p95<=0.85, throughput>=1.20 | Pass/Fail |
| 再現性 |  |  |  | CV<=0.05, checksum一致=100% | Pass/Fail |
| 実装コスト |  |  |  | 合計<=15人日, 再現<=45分 | Pass/Fail |
| 運用差分 |  |  |  | CI増分<=15%, 監視欠落=0, Critical=0 | Pass/Fail |
| 撤収条件 |  |  |  | 該当なし | Pass/Fail |

## 5. 判定

- 最終判定: `Adopt | Reject | Defer`
- 採用/不採用の理由（定量根拠を必須記載）:
- 判定日:
- 適用開始時期（採用時）:
- 再評価期限（Defer時）:

## 6. リスクと緩和策

| リスク | 影響度 | 発生確率 | 緩和策 | オーナー | 期限 |
| --- | --- | --- | --- | --- | --- |
|  | High/Med/Low | High/Med/Low |  |  | YYYY-MM-DD |

## 7. ロールバック/撤収計画

- トリガー条件（撤収条件との対応）:
- ロールバック手順:
- 復旧SLO（目標時間）:
- 影響範囲（CI/運用/開発）:

## 8. 実行計画（採用時）

| フェーズ | 期間 | 完了条件 | 依存タスク |
| --- | --- | --- | --- |
| Phase 1: PoC結果固定 |  |  |  |
| Phase 2: 先行導入 |  |  |  |
| Phase 3: 本番導入判定 |  |  |  |

## 9. 承認

- Decision Owner:
- Reviewer:
- Approver:
- 承認ログ（リンク）:
