# Testing + DDD Docs Index

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

Testing/DDD 関連ドキュメントの索引です。スキーマ、ガイド、PR サマリ、フォーマル/反例/BDD、アダプター、リプレイ関連の参照先を一覧します。

Roadmap
- TESTING-DDD-ROADMAP.md

Schemas
- docs/schemas/artifacts-properties-summary.schema.json
- docs/schemas/artifacts-adapter-summary.schema.json
- docs/schemas/formal-summary.schema.json
- docs/schemas/domain-events.schema.json

Guides
- docs/guides/trace-id.md
- docs/guides/artifacts-normalization.md
- docs/guides/properties-aggregation.md

Quality & PR Summary
- docs/quality/pr-summary.md
- docs/quality/pr-summary-tool.md
- docs/examples/pr-summary/pr-summary.example.ts

Formal / Counterexamples / BDD
- docs/quality/counterexample-gwt.md
- docs/ddd/bdd-lint.md

Adapters
- docs/templates/adapters/README.md
- docs/templates/adapters/ajv-validation.md
- docs/templates/adapters/ajv-failures.md
- docs/templates/adapters/junit-collection.md
- docs/templates/adapters/junit-notes.md
- docs/templates/adapters/*/{summary.json.example,CI.snippet.yml}

Replay
- docs/testing/replay-scripts.md
- docs/testing/replay-coverage.md
- docs/testing/replay-remediation.md
- examples/inventory/artifacts/domain/events.sample.json
- examples/inventory/artifacts/domain/events.replay-failure.sample.json
- examples/inventory/artifacts/formal/summary.sample.json

DDD IR
- docs/ddd/ae-ir-ddd.md
- docs/ddd/events.md

Implementation (scripts)
- scripts/testing/property-harness.mjs
- scripts/testing/replay-runner.mjs
- scripts/bdd/lint.mjs
- scripts/formal/format-counterexamples.mjs
- scripts/adapters/aggregate-artifacts.mjs
