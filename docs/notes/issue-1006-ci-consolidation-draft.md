# Issue #1006: CI Consolidation Strategy v1 (Month 2)

## ステータス
- v1 確定: 2026-01-26
- 更新: 2026-01-28
- 対象: Month 2
- 参考PR: #1769 #1775 #1777 #1778 #1779 #1780 #1781 #1782 #1785 #1786 #1787 #1788 #1789 #1790 #1791 #1792 #1793 #1794 #1795 #1796 #1797 #1798 #1799 #1800 #1801

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
- flake retry dispatch を flake-detect.yml に統合（PR #1777）
- model-checking-manual を formal-verify.yml の workflow_dispatch に統合（PR #1778）
- parallel-test-coordinator を parallel-test-execution.yml の workflow_dispatch に統合（PR #1779）
- nightly-monitoring の監視ジョブを nightly.yml に統合（PR #1775）
- pr-auto-update-branch を pr-ci-status-comment.yml に統合（PR #1780）
- pr-summary-comment を pr-ci-status-comment.yml に統合（PR #1781）
- security schedule を security.yml に統合（PR #1785）
- ci-extended schedule を ci.yml に統合（PR #1786）
- release-quality-artifacts を release.yml に統合（PR #1787）
- formal aggregate を formal-verify の workflow_call に統合（PR #1788）
- spec validation entry を spec-validation.yml に集約（PR #1789）
- full CI の spec validation entry を更新（PR #1790）
- ci.yml に workflow_call の mode/trigger を追加（PR #1791）
- ci consolidation draft update（PR #1792）
- workflow trigger map update（PR #1793）
- workflow overlap candidates update（PR #1794）
- workflow inventory update（PR #1795）
- workflow trigger profiles update（PR #1796）
- ci-fast entry consolidation（PR #1797）
- ci-extended entry consolidation（PR #1798）
- hermetic entry consolidation（PR #1799）
- parallel tests entry consolidation（PR #1800）
- podman smoke entry consolidation（PR #1801）

## 統合スコープと指標
- スコープ: PR ゲート / CI / 検証 / 監査系（schedule/manual）
- 目標: エントリーワークフロー 5-10 に収束（required checks を含む）
- 補足: ユーティリティ系（workflow-lint / branch-protection-apply / agent-commands / pr-ci-status-comment 等）は対象外とし、必要に応じて個別最適を継続

## 統合方針
1) required checks は単独維持（ジョブ再配置のみ、workflow 名は維持）
2) schedule 依存のワークフローは「単一ワークフロー + mode input」へ寄せる
3) workflow_call を提供するワークフローは entry と reusable を分離（呼び出し側の安定性優先）
4) ドキュメントと CLI からの参照に影響するものは、互換 alias を設けて段階移行

## ターゲットセット（エントリー）
以下を Month2 の「統合後のエントリーワークフロー」として定義し、現行の重複や schedule をこの集合へ集約する。

| Group | 現行の主な対象 | Target entry | Required checks 影響 | メモ |
| --- | --- | --- | --- | --- |
| PR gate | verify-lite.yml, copilot-review-gate.yml | verify-lite.yml / copilot-review-gate.yml | あり | 名称は維持、ジョブのみ最適化可 |
| CI core | ci.yml, ci-core.yml, ci-fast.yml, ci-extended.yml, hermetic-ci.yml, minimal-pipeline.yml, ae-ci.yml, pr-verify.yml, verify.yml | ci.yml | なし | mode input で fast/extended/hermetic/qa を切替、reusable は維持 |
| Spec/artifact | spec-check.yml, spec-validation.yml, fail-fast-spec-validation.yml, validate-artifacts-ajv.yml | spec-validation.yml | なし | fail-fast/spec-check を mode 化し、validate-artifacts-ajv は workflow_call として維持 |
| Formal | formal-verify.yml, formal-aggregate.yml, lean-proof.yml | formal-verify.yml | なし | aggregate は workflow_call 化、lean-proof は手動/独立のまま残す |
| Flake/stability | flake-detect.yml, flake-stability.yml | flake-detect.yml | なし | detect/maintenance/retry を mode 化済み。nightly は ops として対象外 |
| Security/compliance | security.yml, sbom-generation.yml, cedar-quality-gates.yml | security.yml | なし | schedule を security.yml へ集約し、sbom/cedar は mode で切替 |
| Release | release.yml, release-quality-artifacts.yml | release.yml | なし | release event + workflow_dispatch を一本化 |

## 移行順序（PR 連投前提）
1) Security schedule 統合（priority A）: security.yml に sbom/cedar の schedule/dispatch を統合（PR #1785）
2) CI core の entry 整理: ci.yml に mode を追加し、ci-fast/ci-extended/ci-core を reusable へ移行（PR #1791 まで実施）
3) Spec/artifact の entry 化: spec-validation.yml に fail-fast/spec-check を mode 化で吸収（PR #1789 / #1790）
4) Formal の entry 化: formal-verify.yml に aggregate を workflow_call で統合（PR #1788）
5) Release の一本化: release-quality-artifacts を release.yml に統合（PR #1787）

## 進捗 (2026-01-28)
- [x] エントリーワークフローの追加統合（ci-fast/ci-extended/hermetic/parallel-tests/podman-smoke）: PR #1797/#1798/#1799/#1800/#1801
- [x] 補助ドキュメントの更新（inventory/trigger map/profiles/overlap）: PR #1793/#1794/#1795/#1796
- [x] consolidation draft 更新: PR #1792

## ロールバック指針
- 1 PR 1 統合を厳守し、各 PR は revert で巻き戻せるようにする
- required checks 名称は変更しない（verify-lite/gate の name を維持）
- 既存のアーティファクト名・summary comment を維持し、差分が出た場合は同 PR で修正

## 残オープン事項
- external automation から参照される workflow の把握（runner/dispatch 依存を棚卸し）
- required checks 以外で「暗黙的に required」扱いされているジョブの確認
