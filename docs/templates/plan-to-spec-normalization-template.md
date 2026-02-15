# Plan -> Spec Normalization Template

> Language / 言語: English | 日本語

Plan (thread/conversation asset) を repository SSOT に正規化するための最小テンプレートです。

## 0. Metadata / メタデータ

- Source thread / plan URL:
- Source PR / issue:
- Normalized by (owner):
- Date (UTC):
- Target repository / branch:
- Related spec path(s):

## 1. Goal and Scope / 目的とスコープ

- Business goal:
- In scope:
- Out of scope:
- Success criteria (high level):

## 2. Requirements Snapshot / 要件スナップショット

- Functional requirements (FR):
  - FR-1:
  - FR-2:
- Constraints:
  - C-1:
  - C-2:
- Assumptions:
  - A-1:
  - A-2:

## 3. Acceptance Criteria (AC) / 受入基準

- AC-1 (Given / When / Then):
- AC-2 (Given / When / Then):
- AC-3 (Given / When / Then):

## 4. Non-Functional Requirements (NFR) / 非機能要件

- Security:
- Reliability:
- Performance:
- Operability:
- Compliance / policy:

## 5. Verification Plan / 検証計画

- Required gates:
  - [ ] lint
  - [ ] test
  - [ ] review gate
  - [ ] verify-lite
- Optional gates (opt-in):
  - [ ] formal
  - [ ] security
  - [ ] adapters
  - [ ] qa
- Test strategy:
  - Unit:
  - Integration:
  - Property / contract:

## 6. Evidence Contract / 証跡契約

- Required evidence:
  - CI run URL:
  - Gate result summary path:
  - Reproduction command(s):
- Optional evidence:
  - Formal report path:
  - Performance report path:
  - Security report path:

## 7. Traceability Map / トレーサビリティ

| Plan item | Spec artifact | Gate / Check | Evidence |
| --- | --- | --- | --- |
| 例: タスクA | `spec/example-spec.md` | `verify-lite` | `artifacts/verify-lite/verify-lite-run-summary.json` |
|  |  |  |  |

補足: Spec artifact path は `docs/spec/registry.md` の配置規約に合わせる。

## 8. Delivery Checklist / 実行チェックリスト

- [ ] Plan 由来の要件が Spec に反映されている
- [ ] AC と NFR がレビュー可能な形で固定されている
- [ ] Required gates の合否が確認済み
- [ ] Evidence が PR から追跡可能
- [ ] Non-goals / out-of-scope が明記されている
