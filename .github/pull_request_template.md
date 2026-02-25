## Summary
- 何を変更したか
- 変更理由（背景/課題）

## Source / Scope
- Issue: #
- 対象範囲（path / workflow / domain）:

## Risk Classification (Required)
- Risk: `risk:low` / `risk:high`
- 判定理由:

## Rollback
- 取り消し手順（revert対象コミット / 無効化手順）:
- 影響最小化策（feature flag / 段階適用）:

## Acceptance Criteria
- [ ] 要件を満たす
- [ ] 既存挙動を壊さない
- [ ] ドキュメント更新済み

## Policy Gate Inputs
- [ ] `verify-lite` が green
- [ ] `policy-gate` が green

### High Risk Only
- [ ] 人間Approve >= 1
- [ ] 変更内容に応じたラベルを付与済み
  - [ ] `run-security`（依存/供給網リスク）
  - [ ] `run-ci-extended`（重い回帰）
  - [ ] `enforce-artifacts`（成果物契約）
  - [ ] `enforce-testing`（再現性/テスト厳格化）
  - [ ] `enforce-context-pack`（依存境界）

## Validation Evidence
- [ ] ローカル確認（実行コマンドを記載）
- [ ] CI確認（workflow/job/主要出力）
- [ ] 失敗時の再現手順（seed/trace/command）

## Notes
- レビュー観点（特に見てほしい箇所）:
