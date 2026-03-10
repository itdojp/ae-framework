---
docRole: derived
canonicalSource:
- schema/counterexample.schema.json
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-03-10'
---
# Counterexample Schema (JSON)

## Purpose
Provide a machine-readable counterexample format that can be validated in CI and reused across verifier backends (TLC / Apalache / conformance).

## Files
- Schema: `schema/counterexample.schema.json`
- Sample: `fixtures/counterexample/sample.counterexample.json`

## Required fields
- `schemaVersion`
- `violated`
- `trace[]`

## Minimal shape
- `violated.kind` should be one of: `INVARIANT`, `LIVENESS`, `THEOREM`, `CONFORMANCE`, `UNKNOWN`
- `violated.name` identifies the violated property
- `trace[]` is an ordered list of steps; each step includes:
  - `index`
  - `state` (free-form object)
  - optional `action`, `meta`

## Validation
- `node scripts/ci/validate-json.mjs` validates the sample along with other schemas in CI.

## Notes
- Backend-specific details should go under `raw` and/or `hints` to keep the core shape stable.

## Linkage convention

Counterexample は core shape を維持したまま、assurance linkage 用の optional field を持てます。

- `claimIds`
- `morphismIds`
- `triageStatus`
- `replayCommand`
- `suggestedContextChanges`

使い分け:
- `claimIds`: 崩れた claim の ID
- `morphismIds`: 関連する Context Pack morphism
- `triageStatus`: `open | resolved | accepted-risk`
- `replayCommand`: 再現用コマンド
- `suggestedContextChanges`: Context Pack suggestion や patch hint への戻し先

補足:
- 既存 backend がこれらを出さない場合、`raw` / `hints` を維持しても構いません。
- `change-package-v2` は既に `counterexamples[].claimIds` を持つため、当面の linkage bridge として利用できます。
- 詳細な運用ルールは `docs/quality/assurance-lanes.md` を参照してください。
