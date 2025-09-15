# CodeX CI/Docs Enhancements Summary (2025-08-27)

> 🌍 Language / 言語: English | 日本語

This change summarizes and documents the recent CodeX integration improvements:

- PR comments now summarize CodeX artifacts:
  - Model Checking: property count and unsatisfied count
  - UI Scaffold: entities, file count, preview (up to 5) with "+N more"
  - Stories: total stories and epics (from summary)
  - Validation: summary text plus Coverage if present
  - Intent: requirements count (from summary)
- Adapter proactive guidance improved with phase-aware nudges (TLA+, OpenAPI, UI summary)
- Artifact schemas and examples are published under `docs/integrations/schemas/*` and `docs/integrations/examples/*`
- Quick Start for CodeX added, including Windows/WSL tips and one-liners

No functional code changes are introduced in this commit; it adds documentation to track the enhancements merged into `main`.


## Related PRs / Issues
- #269: pnpm 統一と CLI ビルド整合
- #270: bin スモークチェック導入（PR/Release）
- #271: bin スモークチェックの他ワークフロー適用
- #273: CodeX 連携 PoC（quickstart/MCP/adaptor/docs）
- #272: CodeX 連携の検討 Issue（本対応の起点）

## Affected CI Workflows
- `PR Verify`: quickstart 実行、CodeX 成果物収集、PR コメント自動投稿
- `Workflow Lint`: YAML 構文・体裁検証（今回の体裁修正を反映）
- その他: 既存の `ae-ci` などは今回の補助機能追加による挙動変更なし

## Local Verification Tips
```bash
# Formal のみ最短（TLA+ / OpenAPI / モデルチェック）
pnpm run build
CODEX_RUN_FORMAL=1 pnpm run codex:quickstart

# UI を phase-state 指定で（既定 dry-run）
pnpm run build
CODEX_RUN_UI=1 CODEX_PHASE_STATE_FILE=samples/phase-state.example.json CODEX_UI_DRY_RUN=1 pnpm run codex:quickstart
```
生成物: `artifacts/codex/`（formal.tla / openapi.yaml / model-check.json / ui-summary.json / result-*.json）

## Example PR Comment (excerpt)
```
### CodeX Artifacts Summary

- Model Checking: 3 properties, Unsatisfied: 1
- UI Scaffold: 3/3 entities, Files: 21 (+6 more), Dry-run: false
  Preview files (up to 5):
    - apps/web/app/products/page.tsx
    - apps/web/app/products/new/page.tsx
    - apps/web/app/products/[id]/page.tsx
    - apps/web/components/ProductForm.tsx
    - apps/web/components/ProductCard.tsx
- Stories: 8 stories, 3 epics
- Validation: Validation Complete - All gates passed, Coverage: 85%
- Intent: 12 requirements
```

## Notes / Caveats
- PR コメントは quickstart の成果物有無に応じて内容が変化します（生成されなかった項目は記載されません）
- Windows 環境では `pnpm run build` 後に quickstart を実行してください（`dist/` 参照）。WSL 推奨、Corepack で pnpm を管理
- 既存のテスト/監査ワークフローの失敗は CodeX 連携機能と独立している可能性があるため、別途ログを確認して個別対応してください
