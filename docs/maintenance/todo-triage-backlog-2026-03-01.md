# TODO Triage Backlog (2026-03-01)

Issue: #2322

## Snapshot
- Markers triaged: 22
- now: 4
- planned: 14
- drop: 4

## Reduction
- 2026-02-28 snapshot: 75 markers
- 2026-03-01 snapshot: 22 markers
- reduced: 53 markers (70.7%)

## Immediate backlog (`triage_status=now`)
- TD-0004 `src/agents/contracts-generator.ts:21` TODO / S2 quality / tracked by #2330
- TD-0005 `src/agents/contracts-generator.ts:24` TODO / S2 quality / tracked by #2330
- TD-0006 `src/agents/contracts-generator.ts:27` TODO / S2 quality / tracked by #2330
- TD-0018 `src/security/sbom-generator.ts:375` TODO / S2 security / tracked by #2329

### Linked issues
- #2329 `[Security] SBOM vulnerability extraction をプレースホルダーから実装へ移行`
- #2330 `[Formal] contracts-generator の仕様由来生成を実装`

## Planned backlog by area (`triage_status=planned`)
- src: 11
- api: 2
- docs: 1

## Dropped marker groups (`triage_status=drop`)
- `tests/unit/scripts/extract-todo-markers.test.ts`: 3 markers
- `tests/unit/docs/check-doc-todo-markers.test.ts`: 1 markers

## Next actions
- #2329, #2330 を優先実装し、完了時に該当マーカーを削除またはIssue参照付きに更新する。
- planned 項目は CLI / Conformance / Public API の3系統で段階処理する。
