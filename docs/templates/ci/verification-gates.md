# Verification Gate Templates

> 🌍 Language / 言語: English | 日本語

---

## English (summary)

This page indexes gate templates for property/contract/mutation/perf.
Use it as a quick map to the canonical commands and evidence locations.

| Gate | Template / Entry | Evidence | Notes |
| --- | --- | --- | --- |
| Property | `docs/templates/spec-kit/property-template.md` | `tests/property/` | fast-check template and invariants |
| Contract | `docs/quality/verification-gates.md` | `artifacts/contracts/` | `pnpm run pipelines:pact` is the default |
| Mutation | `docs/quality/verification-gates.md` | `reports/mutation/` | label `run-mutation` triggers CI Extended |
| Perf/A11y/LH | `docs/quality/adapter-thresholds.md` | `reports/perf-results.json` etc. | thresholds via `enforce-*` labels |

Related references:
- Label gating: `docs/ci/label-gating.md`
- CI Extended overview: `docs/ci/phase2-ci-hardening-outline.md`

---

## 日本語（概要）

property/contract/mutation/perf の検証ゲートを見つけるための索引です。
実行コマンドと成果物パスをここに集約します。

| ゲート | テンプレ / 入口 | 証跡 | 補足 |
| --- | --- | --- | --- |
| Property | `docs/templates/spec-kit/property-template.md` | `tests/property/` | fast-check テンプレ・不変条件 |
| Contract | `docs/quality/verification-gates.md` | `artifacts/contracts/` | 既定は `pnpm run pipelines:pact` |
| Mutation | `docs/quality/verification-gates.md` | `reports/mutation/` | `run-mutation` ラベルで opt-in |
| Perf/A11y/LH | `docs/quality/adapter-thresholds.md` | `reports/perf-results.json` など | `enforce-*` ラベルで強制 |

関連リンク:
- ラベルゲーティング: `docs/ci/label-gating.md`
- CI Extended 概要: `docs/ci/phase2-ci-hardening-outline.md`
