# Issue #1006: CI Consolidation Draft (Month 2)

## 目的
- ワークフロー数の削減と運用負荷の低減
- 必須チェックを維持しつつ、重複実行やスケジュール重複を削減
- PR ゲートと監査系（schedule/manual）の責務を明確化

## 入力
- docs/notes/issue-1006-workflow-inventory.md
- docs/notes/issue-1006-workflow-triggers.md
- docs/notes/issue-1006-workflow-trigger-profiles.md
- docs/notes/issue-1006-workflow-overlap-candidates.md
- docs/ci/branch-protection-operations.md

## 制約
- required checks を維持（Verify Lite / verify-lite, Copilot Review Gate / gate）
- workflow_call で呼び出されるパイプラインの互換性維持
- schedule/manual の監査系を削減する場合は実行意図と通知を維持
- 既存のレポート/アーティファクト出力の互換性維持

## 既存の整理（要旨）
- PR ゲート系 / 監査系 / 手動実行系が混在
- flake 系は reusable 化済みであり、schedule を単一ワークフローへ集約済み（PR #1769）
- flake retry dispatch を flake-detect.yml に統合（mode=retry）
- model-checking-manual を formal-verify.yml の workflow_dispatch に統合（PR #1778 merged）
- parallel-test-coordinator を parallel-test-execution.yml の workflow_dispatch に統合（PR #1779 merged）
- nightly-monitoring の監視ジョブを nightly.yml に統合（PR #1775 merged）
- pr-auto-update-branch を pr-ci-status-comment.yml に統合（PR #1780 merged）
- pr-summary-comment を pr-ci-status-comment.yml に統合（worktree）

## 統合方針
1) required checks は単独維持（ジョブ再配置のみ、workflow 名は維持）
2) schedule 依存のワークフローは「単一ワークフロー + mode input」へ寄せる
3) workflow_call を提供するワークフローは entry と reusable を分離（呼び出し側の安定性優先）
4) ドキュメントと CLI からの参照に影響するものは、互換 alias を設けて段階移行

## 候補とリスク評価
### 低リスク
- schedule 系の統合（flake: detect/maintenance/retry まで完了）
- 手動実行系の統合（model-checking-manual → formal-verify）
- 手動実行系の統合（parallel-test-coordinator → parallel-test-execution）
- 状態コメント/ラベル付与のワークフロー整理（実行結果に影響しないもの）
- PR運用補助の統合（pr-auto-update-branch → pr-ci-status-comment）
- PR要約の統合（pr-summary-comment → pr-ci-status-comment）

### 中リスク
- CI 速度別の分割（ci-fast/ci-extended/ci-core）
  - workflow_call の呼び出し関係を維持しつつ、entry を整理

### 高リスク
- PR ゲートの統合（verify-lite / gate など）
  - required checks の互換性が最優先のため、設計段階で止める

## Month 2 プラン（案）
1) schedule 統合の追加候補を選定し、mode input での切替可否を確認
2) workflow_call の依存関係を確認し、entry 側だけの統合で済む範囲を確定
3) 実行結果の互換性確認（アーティファクト名・summary comment）
4) 低リスクの統合 PR を段階作成（1 PR 1 統合）

## オープン事項
- schedule 統合対象の優先順位
- external automation から参照される workflow の把握
- required checks の名称変更可否
