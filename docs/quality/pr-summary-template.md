---
docRole: derived
canonicalSource:
- docs/quality/pr-summary-tool.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-03-10'
---
# PR Summary Templates (Digest & Detailed)

> 🌍 Language / 言語: English | 日本語
Alerts: {{alerts}}

Digest
```
Quality: {{coverage.value*100 | round}}% (>= {{coverage.threshold*100 | round}}) {{coverage.ok ? '✅' : '❌'}} [{{coverage.delta*100 | sign}}%] | Formal: {{formal.result}} | Adapters: {{adapters.line}} | GWT: {{gwt.count}} | Replay: {{replay.totalEvents}} ev, {{replay.violations.length}} viol | Trace: {{traceIds.join(', ')}} | Gates: {{gates.line}}
```

Detailed
```
## Quality Summary
- Coverage: {{coverage.value*100 | round}}% (>= {{coverage.threshold*100 | round}}) {{coverage.ok ? '✅' : '❌'}}  [{{coverage.delta*100 | sign}}%]
- Failing GWT ({{gwt.count}}): {{gwt.items}}
- Adapters:
{{adapters.list}}
- Formal: {{formal.result}} — {{formal.link}}
- Replay: {{replay.totalEvents}} events ({{replay.byTypeLine}}), {{replay.violations.length}} violations
- Trace IDs: {{traceIds.join(', ')}}

## Verification Gates (optional)
- Mutation: {{mutation.result}} — {{mutation.score}} (>= {{mutation.threshold}})
- Contract: {{contract.result}} — {{contract.link}}
- Property: {{property.result}} — {{property.link}}
- MBT: {{mbt.result}} — {{mbt.link}}
- Performance (perf/a11y/lighthouse): {{performance.result}} — {{performance.summary}}
- Heavy tests (CI Extended aggregate): {{heavy.result}} — {{heavy.link}}
```

Notes
- Inputs should come from normalized artifacts and combined.json (see docs/quality/pr-summary-tool.md).
- Template engine is implementation-defined; variables above illustrate expected fields.
- Include only enabled gates; omit unused sections to keep summaries lean.
