# PR Summary Templates (Digest & Detailed)

Digest
```
Quality: {{coverage.value*100 | round}}% (>= {{coverage.threshold*100 | round}}) {{coverage.ok ? '✅' : '❌'}} [{{coverage.delta*100 | sign}}%] | Formal: {{formal.result}} | Adapters: {{adapters.line}} | GWT: {{gwt.count}} | Replay: {{replay.totalEvents}} ev, {{replay.violations.length}} viol | Trace: {{traceIds.join(', ')}}
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
```

Notes
- Inputs should come from normalized artifacts and combined.json (see docs/quality/pr-summary-tool.md).
- Template engine is implementation-defined; variables above illustrate expected fields.
