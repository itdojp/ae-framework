---
docRole: ssot
lastVerified: '2026-03-23'
owner: project-governance
verificationCommand: pnpm -s run check:doc-consistency
---

# Governance Model / 運営モデル

> 🌍 Language / 言語: English | 日本語

---

## English

### 1. Purpose
This document defines the project-level governance model for `ae-framework`: how technical decisions are fixed, which roles own which responsibilities, and what minimum operating discipline is expected before change is merged.

### 2. Decision-making
- Technical decisions are fixed through repository artifacts such as RFCs, issues, PRs, and SSOT docs.
- Conversation or chat context is not SSOT; the canonical decision must be reflected in repository state.
- Review topology can operate in `team` or `solo` mode depending on repository policy, but important changes must still leave review evidence and merge rationale.
- Security issues are handled privately first and only disclosed through the normal repository flow after the private response path is understood.

### 3. Roles
- **Maintainers**
  - own repository write access, merge decisions, and operational policy changes
  - keep required checks, policy settings, and runbooks aligned
- **Contributors**
  - submit changes through PRs, respond to review, and keep artifacts or docs synchronized with implementation
- **Users**
  - consume the framework, report defects, and provide adoption feedback or improvement requests

### 4. Minimum operating rules
- Fix requirements, acceptance criteria, and important constraints in repository artifacts before relying on automation decisions.
- Keep the current required baseline green before merge; in this repository the daily PR baseline is `verify-lite`, `policy-gate`, and `gate`.
- For higher-risk changes, preserve pre-change and post-change evidence through the current contract set, such as plan artifacts and change packages.
- When automation is used, keep the governing repository variables, runbooks, and actual workflow behavior in sync.

### 5. References
- `docs/ci/pr-automation.md`
- `docs/ci/OPT-IN-CONTROLS.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`

---

## 日本語

### 1. 目的
`ae-framework` におけるプロジェクトレベルの運営モデルを定義します。技術判断をどこに固定するか、各ロールが何を責務として持つか、変更を merge する前に最低限どの運用規律を守るかを扱います。

### 2. 意思決定
- 技術的な意思決定は RFC、Issue、PR、SSOT ドキュメントなどの repo 資産に固定します。
- 会話やチャットの文脈は SSOT ではありません。正は repo 状態へ反映します。
- review topology は repository policy に応じて `team` / `solo` の両方を取り得ますが、重要な変更では review 証跡と merge 根拠を必ず残します。
- セキュリティ課題はまず非公開で対応し、私的な初動整理後に通常の repository flow へ戻します。

### 3. ロール
- **Maintainers（メンテナー）**
  - repository の書き込み権限、merge 判断、運用ポリシー変更を担います
  - required checks、policy 設定、runbook の整合を維持します
- **Contributors（コントリビューター）**
  - PR で変更を提案し、review に対応し、実装と artifacts / docs の整合を保ちます
- **Users（ユーザー）**
  - フレームワークを利用し、不具合報告、採用フィードバック、改善提案を行います

### 4. 最低限の運用ルール
- 要件、受入条件、重要な制約は自動化判断に依存する前に repo 資産へ固定します。
- merge 前には current required baseline を green に保ちます。この repository の日常 PR baseline は `verify-lite`、`policy-gate`、`gate` です。
- 高リスク変更では、plan artifact や Change Package など、current contract に沿った before-change / after-change の証跡を残します。
- 自動化を使う場合は、repository variables、runbook、workflow の実挙動を乖離させません。

### 5. 参照
- `docs/ci/pr-automation.md`
- `docs/ci/OPT-IN-CONTROLS.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
