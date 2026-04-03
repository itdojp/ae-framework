---
docRole: derived
canonicalSource:
- docs/quality/pr-summary-tool.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-03-29'
---
# PR Summary Templates (Digest & Detailed)

> Language / 言語: English | 日本語

---

## English

Use these templates when rendering PR summary comments from normalized artifacts and `combined.json`.

### Alerts line

```text
Alerts: {{alerts}}
```

Render the alerts line only when the summary engine emits alert entries. If no alerts are present, omit the line or render the implementation-defined empty form.

### Digest template

```text
Quality: {{coverage.value*100 | round}}% (>= {{coverage.threshold*100 | round}}) {{coverage.ok ? '✅' : '❌'}} [{{coverage.delta*100 | sign}}%] | Formal: {{formal.result}} | Adapters: {{adapters.line}} | GWT: {{gwt.count}} | Replay: {{replay.totalEvents}} ev, {{replay.violations.length}} viol | Trace: {{traceIds.join(', ')}} | Gates: {{gates.line}}
```

### Detailed template

```text
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

### Notes

- Inputs should come from normalized artifacts and `combined.json` as described in `docs/quality/pr-summary-tool.md`.
- The template engine is implementation-defined. The variables above define the expected field surface, not a specific renderer.
- Include only enabled gates. Omit unused sections to keep the summary compact.
- Artifact lineage and stricter schema rules remain governed by `docs/quality/ARTIFACTS-CONTRACT.md`.

## 日本語

このテンプレートは、正規化済み成果物と `combined.json` から PR summary コメントを生成する際の基準形です。

### Alerts 行

```text
Alerts: {{alerts}}
```

summary 生成処理が alert entry を生成した場合にのみ Alerts 行を出力します。alert がない場合は、その行を省略するか、実装依存の空表現を使います。

### Digest 雛形

```text
Quality: {{coverage.value*100 | round}}% (>= {{coverage.threshold*100 | round}}) {{coverage.ok ? '✅' : '❌'}} [{{coverage.delta*100 | sign}}%] | Formal: {{formal.result}} | Adapters: {{adapters.line}} | GWT: {{gwt.count}} | Replay: {{replay.totalEvents}} ev, {{replay.violations.length}} viol | Trace: {{traceIds.join(', ')}} | Gates: {{gates.line}}
```

### Detailed 雛形

```text
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

### Notes

- 入力は `docs/quality/pr-summary-tool.md` で定義された正規化済み成果物と `combined.json` を前提とします。
- template engine 自体は実装依存です。ここでは renderer 固有仕様ではなく、期待される field surface を示します。
- 有効化されている gate だけを含め、未使用 section は省略して summary を簡潔に保ちます。
- 成果物の lineage や stricter schema rules は `docs/quality/ARTIFACTS-CONTRACT.md` に従います。
