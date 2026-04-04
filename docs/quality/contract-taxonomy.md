---
docRole: derived
canonicalSource:
- docs/reference/CONTRACT-CATALOG.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-04-05'
---
# Contract Taxonomy（DbC / API Contract / Artifacts Contract）

> 🌍 Language / 言語: English | 日本語

---

## English

In ae-framework, the word `contract` appears in multiple contexts. This document defines the canonical taxonomy so PR summaries, runbooks, schema docs, and implementation notes use the term consistently.

### Canonical categories

| Category | Meaning | Typical artifacts / commands |
| --- | --- | --- |
| Design contract (DbC) | Preconditions / postconditions / invariants for behavior/design | Spec Kit, Plan -> Spec template, Context Bundle, runtime conformance checks |
| API/Integration contract | Consumer-driven API contract verification (Pact and related) | `pnpm run pipelines:pact`, CI Extended `pact` smoke, pact test logs/artifacts configured by each project |
| Artifacts contract | Required/optional CI output contract (reports/artifacts presence and shape) | `docs/quality/ARTIFACTS-CONTRACT.md`, `scripts/ci/check-required-artifacts.mjs` |

### Naming guidance

- Use **DbC** or **Design contract** for pre/post/invariant statements.
- Use **Pact contract test** or **API contract verification** for consumer-driven API checks.
- Use **Artifacts contract** only for CI artifact/report obligations.

### Operational interpretation

- In recent verification guides, `contract gate` usually means an API/Integration contract test such as Pact unless the surrounding text explicitly says `DbC` or `Artifacts contract`.
- Legacy labels and guides still use `enforce-contracts` for formal / DbC-oriented enforcement. Treat those paths as DbC-oriented compatibility surfaces, not as Pact/API verification.
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

ae-framework では `contract` が複数の文脈で使われます。本ドキュメントは、PR サマリー、runbook、スキーマ文書、実装メモで用語を一貫させるための基準（SSOT）です。

### 正式な区分

| 区分 | 意味 | 代表的な成果物 / コマンド |
| --- | --- | --- |
| Design contract（DbC） | 振る舞い仕様の事前条件 / 事後条件 / 不変条件 | Spec Kit、Plan -> Spec 雛形、Context Bundle、runtime conformance 検査 |
| API/Integration contract | Pact などのコンシューマ駆動 API 契約検証 | `pnpm run pipelines:pact`、CI Extended の `pact` smoke、各プロジェクトで定義された Pact log / artifact |
| Artifacts contract | CI 成果物（reports/artifacts）の必須 / 任意ルール | `docs/quality/ARTIFACTS-CONTRACT.md`、`scripts/ci/check-required-artifacts.mjs` |

### 表記ガイド

- DbC（pre/post/invariant）を指す場合は **DbC** または **Design contract** を使います。
- API 契約検証を指す場合は **Pact contract test** または **API contract verification** を使います。
- 成果物の必須要件を指す場合のみ **Artifacts contract** を使います。

### 運用上の解釈

- 直近の verification guide で `contract gate` とだけ書かれている場合、周辺文脈に `DbC` または `Artifacts contract` の明示がなければ、通常は Pact のような API/Integration contract test を指します。
- `enforce-contracts` のような legacy label / command は、formal / DbC 系 enforcement の互換面として扱います。Pact / API verification と同義ではありません。
- DbC は単一 workflow や単一 label ではありません。property testing、runtime conformance、request validation、assertion-heavy integration tests など複数の check で証跡化されます。
- Artifacts contract は期待される CI 出力の有無と shape を統制しますが、それ自体で business behavior を証明するものではありません。

### 互換性メモ

- 既存の label / command / 歴史的文書には、互換性のために `contract` という裸の語が残っています。
- まずは本文上の意味分離を優先します。command や label の破壊的 rename は、明示的な migration plan がある場合に限って実施します。

### 関連ドキュメント

- `docs/quality/verification-gates.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/ci-policy.md`
- `docs/architecture/RUNTIME-CONFORMANCE-DESIGN.md`
