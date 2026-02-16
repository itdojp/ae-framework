# Plan -> Spec Normalization Sample

> This file is an example filled from `plan-to-spec-normalization-template.md`.

## 0. Metadata / メタデータ

- Source thread / plan URL: `issue #1971` (sample)
- Source PR / issue: `#1971`
- Normalized by (owner): docs maintainer
- Date (UTC): 2026-02-15
- Target repository / branch: `ae-framework / docs/1971-thread-repo-ci-normalization`
- Related spec path(s): `spec/gates.yaml`, `docs/quality/ARTIFACTS-CONTRACT.md`

## 1. Goal and Scope / 目的とスコープ

- Business goal: Plan から Spec 固定までの手順を標準化し、レビューで追跡可能にする。
- In scope: 手順ガイド、テンプレ適用例、PRレビュー観点。
- Out of scope: 新規CIジョブ追加、既存ゲート基準の変更。
- Success criteria (high level): Thread -> Repo -> CI の手順が再現可能である。

## 2. Requirements Snapshot / 要件スナップショット

- Functional requirements (FR):
  - FR-1: Planの内容をテンプレートの各欄へ正規化する。
  - FR-2: PR時に Plan->Spec->Gate->Evidence の対応を記載する。
- Constraints:
  - C-1: 既存CI構成を壊さない。
  - C-2: ドキュメント変更のみで完結する。
- Assumptions:
  - A-1: verify-lite と review gate が運用中である。
  - A-2: PR本文にトレーサビリティ欄を記載できる。

### 2.1 Design by Contract (DbC) / 契約条件

- Preconditions（PRE-*）:

| ID | Statement | Violation behavior |
| --- | --- | --- |
| PRE-001 | PR本文に対象の Plan URL と関連 Spec path が記載されていること。 | review gate で差し戻し、PRコメントで不足項目を明示する。 |

- Postconditions（POST-*）:

| ID | Statement | Violation behavior |
| --- | --- | --- |
| POST-001 | Plan -> Spec -> Gate -> Evidence の対応が PR から追跡可能であること。 | verify-lite 結果共有を保留し、追記後に再レビューする。 |

- Invariants（INV-*）:

| ID | Statement | Enforcement location（どこで担保するか） | Violation behavior |
| --- | --- | --- | --- |
| INV-001 | Required gates（verify-lite/review gate）の確認を省略しないこと。 | PRテンプレチェック + review gate。 | `do-not-merge` の維持。 |

## 3. Acceptance Criteria (AC) / 受入基準

- AC-1 (Given / When / Then):  
  Given Plan入力がある  
  When 正規化テンプレートを適用する  
  Then Spec/AC/NFR/検証計画がrepo上で確認できる。

- AC-2 (Given / When / Then):  
  Given PRレビューを行う  
  When PR本文を確認する  
  Then Plan->Spec->Gate->Evidence対応を追跡できる。

- AC-3 (Given / When / Then):  
  Given CIが失敗する  
  When 失敗時手順に従う  
  Then 再実行とEvidence更新が完了する。

## 4. Non-Functional Requirements (NFR) / 非機能要件

- Security: 機密情報をテンプレートに含めない。
- Reliability: 手順を複数PRで再利用可能にする。
- Performance: 追加の重いCIを必須化しない。
- Operability: 失敗時の再実行手順を明記する。
- Compliance / policy: required gate 運用を維持する。

## 5. Verification Plan / 検証計画

- Required gates:
  - [x] lint
  - [x] test
  - [x] review gate
  - [x] verify-lite
- Optional gates (opt-in):
  - [ ] formal
  - [ ] security
  - [ ] adapters
  - [ ] qa
- Test strategy:
  - Unit: n/a（ドキュメント変更）
  - Integration: n/a（ドキュメント変更）
  - Property / contract: 既存契約ドキュメントとの整合を確認
  - Runtime conformance: n/a（ドキュメント変更）
  - Pact / API contract: n/a（ドキュメント変更）

- DbC verification mapping:

| Contract ID | Type | Verification (test/gate) | Evidence |
| --- | --- | --- | --- |
| PRE-001 | precondition | Copilot Review Gate / checklist review | PR review thread |
| POST-001 | postcondition | verify-lite summary確認 | `artifacts/verify-lite/verify-lite-run-summary.json` |
| INV-001 | invariant | Required gate確認（review gate + verify-lite） | Required checks status |

## 6. Evidence Contract / 証跡契約

- Required evidence:
  - CI run URL: PRごとに記録
  - Gate result summary path: `artifacts/verify-lite/verify-lite-run-summary.json`
  - Reproduction command(s): `pnpm types:check && pnpm lint && pnpm build`
- Optional evidence:
  - Formal report path: `artifacts/hermetic-reports/formal/summary.json`
  - Performance report path: n/a
  - Security report path: opt-in 時のみ

## 7. Traceability Map / トレーサビリティ

| Plan or Contract item | Spec artifact | Gate / Check | Evidence |
| --- | --- | --- | --- |
| Thread->Repo手順の定義 | `docs/guides/THREAD-REPO-CI-FLOW.md` | review gate | PR review thread |
| テンプレ適用例の追加 | `docs/templates/plan-to-spec-normalization-sample.md` | verify-lite | CI summary artifact |
| PRE-001 / POST-001 / INV-001 | `docs/templates/plan-to-spec-normalization-template.md` | review gate + verify-lite | Required checks status |

## 8. Delivery Checklist / 実行チェックリスト

- [x] Plan 由来の要件が Spec に反映されている
- [x] AC と NFR がレビュー可能な形で固定されている
- [x] PRE/POST/INV と違反時挙動が明記されている
- [x] Required gates の合否が確認済み
- [x] Evidence が PR から追跡可能
- [x] Non-goals / out-of-scope が明記されている
