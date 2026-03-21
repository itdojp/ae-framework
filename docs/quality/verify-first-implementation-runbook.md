---
docRole: ssot
lastVerified: '2026-03-21'
owner: verify-first
verificationCommand: pnpm -s run check:doc-consistency
---
# Verify-first Implementation Runbook

> 🌍 Language / 言語: English | 日本語

---

## English

### 1. Purpose

Define the shortest reproducible operating flow for implementing Verify-first in real projects.

Scope:
- Spec-driven test skeleton generation
- required / opt-in gate execution
- reproducible operation with or without Codex

### 2. Preconditions

- Plan to Spec normalization has already been completed according to `docs/templates/plan-to-spec-normalization-template.md`
- The required gate baseline has been reviewed in `docs/quality/verify-first-gate-baseline.md`
- The evidence contract has been reviewed in `docs/quality/ARTIFACTS-CONTRACT.md`

### 3. Standard Flow

#### Step 1: Fix Plan into repository SSOT

1. Commit requirements, acceptance criteria, NFRs, and constraints into repository-managed artifacts.
2. Fill the traceability map.
3. Record the source issue / thread in the PR description.

#### Step 2: Generate test skeletons

Create the minimum test skeletons from the acceptance criteria in the spec.

Status note:
- `ae tests:scaffold` is an implementation item from Issue #1979 and is not available in environments that predate the merge of that feature.

```bash
# Example: in environments where the scaffold command is available, point it at your project spec or normalized plan artifact
ae tests:scaffold --input path/to/your-spec.md
```

If `ae tests:scaffold` is unavailable, manually expand `docs/templates/spec-kit/*` and create equivalent skeletons.

Typical generated outputs:
- `tests/generated/spec-kit/<spec-id>/bdd/<spec-id>.feature`
- `tests/generated/spec-kit/<spec-id>/<spec-id>.acceptance.md`
- `tests/generated/spec-kit/<spec-id>/property/<spec-id>.property.test.ts`
- `tests/generated/spec-kit/<spec-id>/contract/<spec-id>.contract.test.ts`
- `tests/generated/spec-kit/<spec-id>/regression/<spec-id>.regression.test.ts`

Placement and update rules:
- Keep generated skeletons under `tests/generated/spec-kit/<spec-id>/`
- Separate generated skeletons from handwritten production tests
- When acceptance criteria change, regenerate with overwrite and review the diff explicitly

#### Step 3: Run required gates

```bash
pnpm run verify:lite
```

For PR handling, treat required gates as fail-closed and do not merge while they are failing.

#### Step 4: Add opt-in gates when needed

Apply `run-formal`, `run-security`, `run-adapters`, or `run-qa` according to change risk and scope.

Use `docs/quality/verify-first-gate-baseline.md` as the decision baseline.

#### Step 5: Fix evidence

When a gate fails, use:
- `docs/quality/verify-first-failure-diagnostic-template.md`

Always retain:
- the failed gate
- the reproduction command
- links to the related spec / policy
- CI run URL and artifact path

For PR comment integration, see:
- `docs/quality/verify-first-failure-comment-design.md`

### 4. Operation With / Without Codex

#### With Codex

- Codex may help author or normalize plans
- The SSOT remains repository artifacts such as Spec / AC / NFR / Evidence

#### Without Codex

- The same flow must remain reproducible with CLI and CI only
- At minimum, operations should remain capable of passing `verify-lite`, `policy-gate`, and `gate`

### 5. Checklist

- [ ] Plan to Spec normalization is complete
- [ ] Acceptance-criteria-driven skeletons are generated
- [ ] Required gates are green
- [ ] The rationale for any opt-in gate selection is recorded
- [ ] Evidence can be reached from the PR

### 6. References

- `docs/guides/THREAD-REPO-CI-FLOW.md`
- `docs/quality/verify-first-artifacts-catalog.md`
- `docs/quality/verify-first-gate-baseline.md`
- `docs/quality/verify-first-failure-diagnostic-template.md`
- `docs/quality/verify-first-failure-comment-design.md`
- `docs/integrations/CODEX-VENDOR-NEUTRAL-BOUNDARY.md`

---

## 日本語

## 1. 目的

本Runbookは、Verify-firstを実装運用に落とすための最短手順を定義します。  
対象は、Issue #1979 で扱う以下の実装領域です。

- Spec起点のテスト雛形生成
- Required / Opt-in ゲート運用
- Codex連携あり/なしの再現可能運用

## 2. 前提

- `docs/templates/plan-to-spec-normalization-template.md` に沿って Plan -> Spec を正規化済み
- Requiredゲート方針を `docs/quality/verify-first-gate-baseline.md` で確認済み
- 証跡契約を `docs/quality/ARTIFACTS-CONTRACT.md` で確認済み

## 3. 標準フロー（実装）

### Step 1: Plan -> Spec 固定

1. 要件/AC/NFR/制約を repo に固定する。  
2. `Traceability Map` を埋める。  
3. PR本文に source issue/thread を記載する。

### Step 2: テスト雛形生成

Spec の AC から、最小のテスト雛形を作成する。

> ステータス注記（2026-02-15時点）: `ae tests:scaffold` は Issue #1979 の実装項目で、PR #1980 が未マージの環境では利用不可です。

```bash
# 例: 実装済み環境（PR #1980 以降）では AC から bdd/property/acceptance map を生成
ae tests:scaffold --input docs/templates/plan-to-spec-normalization-sample.md
```

`ae tests:scaffold` が未実装の環境では、`docs/templates/spec-kit/*` を手動展開して同等の雛形を作成する。

生成される成果物（例）:
- `tests/generated/spec-kit/<spec-id>/bdd/<spec-id>.feature`
- `tests/generated/spec-kit/<spec-id>/<spec-id>.acceptance.md`
- `tests/generated/spec-kit/<spec-id>/property/<spec-id>.property.test.ts`
- `tests/generated/spec-kit/<spec-id>/contract/<spec-id>.contract.test.ts`
- `tests/generated/spec-kit/<spec-id>/regression/<spec-id>.regression.test.ts`

配置規約と更新ルール（最小）:
- 雛形生成物は `tests/generated/spec-kit/<spec-id>/` 配下に集約し、手動作成の本実装テストとは分離する。
- AC変更時は `ae tests:scaffold ... --overwrite` で再生成し、差分レビューで必要な手修正を反映する。
- `*.acceptance.md` は AC とテスト成果物パスの対応表として維持し、PR で必ず更新有無を確認する。

### Step 3: Required ゲート実行

```bash
pnpm run verify:lite
```

PRでは Required を fail-closed とし、未通過のまま merge しない。

### Step 4: Opt-in ゲート追加（必要時）

変更内容に応じて `run-formal`, `run-security`, `run-adapters`, `run-qa` を適用する。  
基準は `docs/quality/verify-first-gate-baseline.md` を正とする。

### Step 5: Evidence 固定

失敗時は `docs/quality/verify-first-failure-diagnostic-template.md` を使用し、以下を必ず残す。

- 失敗ゲート
- 再現コマンド
- 関連Spec/Policyリンク
- CI run URL と artifact path

PR自動コメントへの連携案は `docs/quality/verify-first-failure-comment-design.md` を参照。

## 4. Codex連携あり/なしの運用

### Codex連携あり

- Plan作成/整理はCodexで実施可能  
- ただし SSOT は repo 成果物（Spec/AC/NFR/Evidence）

### Codex連携なし

- 同じフローをCLI/CIのみで再現可能であることを要件とする  
- 最低限 `verify-lite` / `policy-gate` / `gate` を通過できる運用を維持する

## 5. チェックリスト

- [ ] Plan -> Spec の固定が完了している
- [ ] AC起点のテスト雛形を生成済み
- [ ] Requiredゲートが成功している
- [ ] 必要なOpt-inゲートの判定理由を記録した
- [ ] Evidence を PR から辿れる

## 6. 参照

- `docs/guides/THREAD-REPO-CI-FLOW.md`
- `docs/quality/verify-first-artifacts-catalog.md`
- `docs/quality/verify-first-gate-baseline.md`
- `docs/quality/verify-first-failure-diagnostic-template.md`
- `docs/quality/verify-first-failure-comment-design.md`
- `docs/integrations/CODEX-VENDOR-NEUTRAL-BOUNDARY.md`
