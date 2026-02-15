# Verify-first Failure Diagnostic Template

> PR/CI 失敗時の最小診断テンプレート（再現手順付き）

## 0. Context

- PR / Issue:
- Commit SHA:
- Failed gate:
- Detection time (UTC):

## 1. Symptom / 現象

- Error summary:
- First failing step:
- Scope (files/modules):

## 2. Impact / 影響

- Blocking level: Required / Opt-in
- User impact:
- Release impact:

## 3. Reproduction / 再現

- Local command(s):
  ```bash
  # 例
  pnpm types:check && pnpm lint && pnpm build
  ```
- Expected:
- Actual:

## 4. Spec/Policy linkage

- Related spec path(s):
- Related acceptance criteria:
- Related policy/contract:

## 5. Root-cause hypothesis / 原因仮説

- Hypothesis-1:
- Hypothesis-2:

## 6. Fix plan / 対処計画

- Immediate fix:
- Additional tests/checks:
- Rollback plan (if needed):

## 7. Evidence / 証跡

- CI run URL:
- Artifact path(s):
- Log excerpt location:

## 8. Decision

- [ ] Re-run only
- [ ] Fix + re-run
- [ ] Fail-open (temporary) + follow-up issue
- Follow-up issue (required for fail-open):
