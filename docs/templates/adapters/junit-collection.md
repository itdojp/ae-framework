---
docRole: ssot
lastVerified: '2026-03-12'
owner: templates-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# JUnit + Summary Collection Flow (#408)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

JUnit XML（生）と正規化 JSON の双方を生成し、JSON を PR 集約の唯一の入力として使用します。XML の解析はコア外（アダプター/CI）に留めます。

- Produce both raw JUnit XML and normalized JSON summary.
- Upload both as CI artifacts; aggregate PR summary from JSON only.

```mermaid
%% no-doctest
flowchart TD
  A[Run tests] --> B[Generate junit.xml]
  A --> C[Write artifacts/<adapter>/summary.json]
  B --> D[Upload junit.xml]
  C --> E[Upload summary.json]
  E --> F[PR Summary Aggregator]
```

Notes
- Keep XML parsing out of core; use JSON summaries for aggregation.
- Include `traceId` in JSON where applicable.
