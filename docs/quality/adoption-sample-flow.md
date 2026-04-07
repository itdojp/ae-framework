---
docRole: derived
canonicalSource:
- docs/quality/verify-first-implementation-runbook.md
- docs/product/MINIMAL-ADOPTION.md
lastVerified: '2026-04-07'
---
# Ownership & Adoption Sample Flow

> 🌍 Language / 言語: English | 日本語

---

## English

Purpose: Provide a minimal end-to-end flow that teams can follow when adopting ae-framework for AI-assisted changes.

## Flow (minimal)

### 1) Context bundle
- Build a context bundle using `docs/guides/context-bundle.md`
- Validate required context with `docs/guides/context-vacuum-checklist.md`

### 2) Spec kit
- Draft a spec using the appropriate template:
  - feature: `docs/templates/spec-kit/feature-spec-kit.md`
  - bugfix: `docs/templates/spec-kit/bugfix-spec-kit.md`
  - refactor: `docs/templates/spec-kit/refactor-spec-kit.md`

### 3) Blueprint
- Create a blueprint from `docs/templates/blueprint/blueprint-template.md`
- Record ownership, risks, and rollback plan

### 4) Implementation and verify
- Implement changes and run Verify Lite as the baseline
- Opt in to heavier gates when needed by using labels described in `docs/ci/label-gating.md`

### 5) Evidence
- Generate a PR summary using `docs/quality/pr-summary-template.md`
- Attach artifacts or links following `docs/quality/pr-summary-tool.md`

### 6) Review
- Apply `docs/quality/llm-first-review-checklist.md`
- Enforce `docs/quality/guarded-automation-template.md`
- Confirm Ownership DoD with `docs/quality/ownership-dod.md`

## Expected artifacts
- Context bundle
- Spec (feature, bugfix, or refactor)
- Blueprint with ownership and rollback plan
- PR summary with links to verification artifacts

## Notes
- This flow assumes verify-then-merge with human approval.
- Keep evidence short in the PR and link to detailed artifacts instead of duplicating raw output.

---

## 日本語

目的: AI 支援で変更を進める際に、ae-framework を導入するチームが辿る最小限の一連フローを示します。

## フロー（最小構成）

### 1) Context bundle
- `docs/guides/context-bundle.md` を使って context bundle を作成する
- `docs/guides/context-vacuum-checklist.md` で必要な前提情報が揃っているか検証する

### 2) Spec kit
- 変更種別に応じたテンプレートで spec を作成する
  - feature: `docs/templates/spec-kit/feature-spec-kit.md`
  - bugfix: `docs/templates/spec-kit/bugfix-spec-kit.md`
  - refactor: `docs/templates/spec-kit/refactor-spec-kit.md`

### 3) Blueprint
- `docs/templates/blueprint/blueprint-template.md` を基に blueprint を作成する
- 責務分界、リスク、ロールバック計画を記録する

### 4) 実装と検証
- 変更を実装し、最低限の基準として Verify Lite を実行する
- 必要に応じて `docs/ci/label-gating.md` に従い、より重いゲートをラベルで有効化する

### 5) 証跡
- `docs/quality/pr-summary-template.md` を使って PR サマリーを作成する
- `docs/quality/pr-summary-tool.md` に従って成果物やリンクを添付する

### 6) レビュー
- `docs/quality/llm-first-review-checklist.md` を適用する
- `docs/quality/guarded-automation-template.md` の条件を満たす
- `docs/quality/ownership-dod.md` で Ownership DoD を確認する

## 期待される成果物
- Context bundle
- Spec（feature、bugfix、または refactor）
- 責務分界とロールバック計画を含む blueprint
- 検証成果物へのリンクを含む PR サマリー

## 備考
- このフローは人手承認を伴う verify-then-merge 運用を前提とする
- PR には要点のみを記載し、詳細は成果物へのリンクで示す
