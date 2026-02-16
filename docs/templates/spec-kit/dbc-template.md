# Spec Kit: Design by Contract (DbC) Template

> Language / 言語: English | 日本語

DbC（precondition / postcondition / invariant）を仕様として固定し、テスト・ゲート・証跡へ接続するためのテンプレートです。

## 1) Meta / メタ情報
- Scope（function / API / entity / workflow）:
- Owner:
- Risk level（low / medium / high）:
- Related FR / AC / NFR:
- Related spec path(s):

## 2) Preconditions / 事前条件

| ID | Statement | Violation behavior | Test mapping |
| --- | --- | --- | --- |
| PRE-001 |  |  |  |
| PRE-002 |  |  |  |

## 3) Postconditions / 事後条件

| ID | Statement | Observable output / side effect | Violation behavior | Test mapping |
| --- | --- | --- | --- | --- |
| POST-001 |  |  |  |  |
| POST-002 |  |  |  |  |

## 4) Invariants / 不変条件

| ID | Statement | Enforcement location | Violation behavior | Test mapping |
| --- | --- | --- | --- | --- |
| INV-001 |  | runtime / db / property |  |  |
| INV-002 |  | runtime / db / property |  |  |

## 5) Verification Mapping / 検証マッピング

| Contract ID | Test file / suite | Gate / Check | Evidence path |
| --- | --- | --- | --- |
| PRE-001 |  | unit / integration / verify-lite |  |
| POST-001 |  | integration / conformance |  |
| INV-001 |  | property / runtime conformance / db constraint |  |

## 6) Evidence / 証跡
- Reproduction command(s):
- CI run URL:
- Required artifacts:
  - `artifacts/verify-lite/verify-lite-run-summary.json`
- Optional artifacts:
  - `artifacts/properties/`
  - `artifacts/contracts/`
  - `artifacts/hermetic-reports/conformance/`

## 7) Notes / 運用メモ
- DbCは「条件の定義と検証接続」を扱います。
- property template（`property-template.md`）は「実装テスト雛形」を扱います。
- API契約検証（Pact）と用語を混同しないよう `docs/quality/contract-taxonomy.md` を参照してください。

## 8) Related Docs / 関連ドキュメント
- `docs/templates/plan-to-spec-normalization-template.md`
- `docs/quality/verification-gates.md`
- `docs/guides/context-bundle.md`
