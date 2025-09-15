# CI Labels — Cheatsheet

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

PR ラベルの早見表です。`enforce-*` 系でブロッキング化、`coverage:<pct>` で閾値設定、`trace:<id>` で特定トレースに集中、`pr-summary:detailed` で詳細ビュー。詳細は `docs/ci/label-gating.md` を参照。

- enforce-artifacts — make artifacts validation blocking
- enforce-testing — make testing scripts (property/replay/BDD lint) blocking
- enforce-coverage — make coverage threshold blocking
- coverage:<pct> — set coverage threshold (default 80)
- trace:<id> — focus property/replay runs (e.g., trace:inv-001)
- pr-summary:detailed — detailed PR summary view

Markers (auto-labels)
- [detailed] — adds pr-summary:detailed
- [enforce-coverage] — adds enforce-coverage
- [cov=85] — adds coverage:85

Docs
- See docs/ci/label-gating.md for full details.
