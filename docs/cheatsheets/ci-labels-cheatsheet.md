# CI Labels — Cheatsheet

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
