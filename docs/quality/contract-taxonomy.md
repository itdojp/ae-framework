---
docRole: derived
canonicalSource:
- docs/reference/CONTRACT-CATALOG.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-03-22'
---
# Contract Taxonomy（DbC / API Contract / Artifacts Contract）

> 🌍 Language / 言語: English | 日本語

---

## English

In ae-framework, the word `contract` appears in multiple contexts. This document defines the canonical taxonomy so PR summaries, runbooks, schema docs, and implementation notes use the term consistently.

### Canonical categories

| Category | Meaning | Typical artifacts / commands |
| --- | --- | --- |
| Design contract (DbC) | Preconditions / postconditions / invariants for behavior/design | Spec Kit, Plan->Spec template, Context Bundle, runtime conformance checks |
| API/Integration contract | Consumer-driven API contract verification (Pact and related) | `pnpm run pipelines:pact`, CI Extended `pact` smoke, pact test logs/artifacts configured by each project |
| Artifacts contract | Required/optional CI output contract (reports/artifacts presence and shape) | `docs/quality/ARTIFACTS-CONTRACT.md`, `scripts/ci/check-required-artifacts.mjs` |

### Naming guidance

- Use **DbC** or **Design contract** for pre/post/invariant statements.
- Use **Pact contract test** or **API contract verification** for consumer-driven API checks.
- Use **Artifacts contract** only for CI artifact/report obligations.

### Operational interpretation

- When a verification guide mentions `contract gate`, read it as an API/Integration contract test unless the surrounding text explicitly says `DbC` or `Artifacts contract`.
- DbC is not a single workflow or a single label. It is evidenced by multiple checks such as property testing, runtime conformance, request validation, and assertion-heavy integration tests.
- Artifacts contract governs whether expected CI outputs exist and match the required shape. It does not prove business behavior by itself.

### Compatibility note

- Existing labels, commands, and historical documents may still include the bare word `contract` for backward compatibility.
- Prefer text-level clarification first. Renaming commands or labels should happen only through an explicit migration plan.

### Related documents

- `docs/quality/verification-gates.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/ci-policy.md`
- `docs/architecture/RUNTIME-CONFORMANCE-DESIGN.md`

---

## 日本語

ae-framework では `contract` が複数の意味で使われます。本ドキュメントを用語の基準（SSOT）とします。

| 区分 | 意味 | 代表的な成果物 / コマンド |
| --- | --- | --- |
| Design contract（DbC） | 振る舞い仕様の事前条件 / 事後条件 / 不変条件 | Spec Kit、Plan->Spec テンプレ、Context Bundle、Runtime Conformance |
| API/Integration contract | Pact などの consumer-driven API 契約検証 | `pnpm run pipelines:pact`、CI Extended の pact smoke、プロジェクトで定義された pact のログ/成果物 |
| Artifacts contract | CI成果物（reports/artifacts）の必須/任意ルール | `docs/quality/ARTIFACTS-CONTRACT.md`、`scripts/ci/check-required-artifacts.mjs` |

表記ルール:
- DbC（pre/post/invariant）を指す場合は **DbC** または **Design contract** を使う。
- API契約検証を指す場合は **Pact contract test** または **API contract verification** を使う。
- 成果物の必須要件を指す場合のみ **Artifacts contract** を使う。

互換性メモ:
- 既存のラベル/コマンド名に `contract` を含むものは互換性のため当面維持する。
- まずは文書上の意味分離を優先し、破壊的リネームは別Issueで扱う。

## 関連ドキュメント

- `docs/quality/verification-gates.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/ci-policy.md`
- `docs/architecture/RUNTIME-CONFORMANCE-DESIGN.md`
