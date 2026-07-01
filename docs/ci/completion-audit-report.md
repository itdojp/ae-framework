---
docRole: ssot
lastVerified: '2026-07-01'
owner: ci-governance
verificationCommand: pnpm -s run audit:completion -- --input fixtures/audit/completion/pr-3566-closeout.input.json --generated-at 2026-07-01T00:00:00.000Z --no-write
---
# Completion Audit Report

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

A completion audit report records the final closeout evidence for a PR after review threads and CI checks have been handled. It exists because a PR can be mergeable when required merge checks pass while advisory workflow findings, skipped runs, or stale runs are still visible in GitHub surfaces.

The audit makes this wording precise:

- **Required merge checks** decide merge eligibility together with branch protection and human review.
- **Advisory workflow findings** are visible evidence and may require follow-up, but are not the same as required-check failure.
- **Skipped workflow runs** are recorded separately so completion comments do not imply that every optional surface executed.
- **Stale workflow runs** identify older-head cancelled or failed runs that were superseded by a later clean head.
- **Local verification** records commands the maintainer ran before or during PR stabilization.

The report is evidence only. It does not approve, merge, waive findings, or change policy-gate enforcement.

### 2. Contract and renderer

| Surface | Value |
| --- | --- |
| Schema | `schema/completion-audit-report.schema.json` (`completion-audit-report/v1`) |
| Renderer | `scripts/audit/render-completion-audit.mjs` |
| Package script | `pnpm run audit:completion` |
| Default input fixture | `fixtures/audit/completion/pr-3566-closeout.input.json` |
| Default output JSON | `artifacts/audit/completion-audit-report.json` |
| Default output Markdown | `artifacts/audit/completion-audit-report.md` |

The renderer is offline-only. It reads local JSON input and does not call live GitHub APIs. If live PR state is needed, collect it separately and preserve the captured source in the input fixture or task ledger.

### 3. Deterministic fixture run

```bash
pnpm run audit:completion -- \
  --input fixtures/audit/completion/pr-3566-closeout.input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/audit/completion-audit-report.json \
  --output-md artifacts/audit/completion-audit-report.md
```

For a read-only preview suitable before posting a PR/Issue comment:

```bash
pnpm run audit:completion -- \
  --input fixtures/audit/completion/pr-3566-closeout.input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --no-write
```

The checked-in #3556/#3566 fixture demonstrates the intended distinction: `gate`, `policy-gate`, and `verify-lite` are required merge checks and passed on the final head, while advisory vulnerability/security observations and stale earlier gate runs are recorded outside the required-check decision.

### 4. Completion comment wording

Use the Markdown output as the pasteable audit body or link to the JSON/Markdown artifacts. Prefer precise statements such as:

- `Required checks passed on final head <sha>.`
- `Review completeness was status=ok with zero unresolved review threads.`
- `Advisory workflow findings are listed in the completion audit and are not represented as required-check failures.`
- `The audit is report-only and does not grant approval or waive follow-up work.`

Avoid broad statements such as `all workflows were clean` unless both required and advisory surfaces were inspected and no advisory findings remained.

### 5. Relationship to Evidence Sprint

This report enables the Evidence Sprint self-dogfood and public case-study flow. Later evidence artifacts should link the completion audit so readers can follow the chain from Issue intent to PR closeout without confusing required merge checks with advisory workflow-run findings.

---

## 日本語

### 1. 目的

completion audit report は、レビューthreadとCI対応後のPR closeout証跡を記録するための report-only artifact です。required merge check が通ってマージ可能な状態でも、advisory workflow finding、skipped run、stale run がGitHub上に残る場合があります。このartifactは、その差分を明示的に分離します。

- **Required merge checks** は branch protection と人間レビューと合わせて merge eligibility を決める。
- **Advisory workflow findings** は追跡すべき証跡だが、required check failure とは別に扱う。
- **Skipped workflow runs** は任意surfaceが未実行だった事実として記録する。
- **Stale workflow runs** は旧headのcancelled/fail runが新headで置き換わったことを示す。
- **Local verification** はmaintainerが実行したローカル検証コマンドを記録する。

このreportは証跡であり、承認・マージ・waiver・policy-gate enforcement変更の権限は持ちません。

### 2. 使い方

```bash
pnpm run audit:completion -- \
  --input fixtures/audit/completion/pr-3566-closeout.input.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --no-write
```

PR/Issueコメントには、Markdown出力を貼り付けるか、JSON/Markdown artifactへのリンクを記録します。完了コメントでは `required checks passed` と `advisory findings remain` を分けて記述してください。
