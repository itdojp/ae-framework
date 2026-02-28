# TODO Triage Backlog (2026-02-28)

Issue: #2322

## Snapshot
- Markers triaged: 75
- now: 4
- planned: 14
- drop: 57

## Classification policy applied
- `now`: 実装不足が直接機能品質/セキュリティに影響する項目
- `planned`: 影響が限定的で、計画修正する項目
- `drop`: テンプレート/サンプル/テスト用の意図的マーカー（負債管理対象外）

## Immediate backlog (`triage_status=now`)
- TD-0034 `src/agents/contracts-generator.ts:21` TODO / S2 quality / tracked by #2330
- TD-0035 `src/agents/contracts-generator.ts:24` TODO / S2 quality / tracked by #2330
- TD-0036 `src/agents/contracts-generator.ts:27` TODO / S2 quality / tracked by #2330
- TD-0061 `src/security/sbom-generator.ts:375` TODO / S2 security / tracked by #2329

### Linked issues
- #2329 `[Security] SBOM vulnerability extraction をプレースホルダーから実装へ移行`
- #2330 `[Formal] contracts-generator の仕様由来生成を実装`

## Planned backlog by area (`triage_status=planned`)
- src: 11
- api: 2
- docs: 1

## Dropped marker groups (`triage_status=drop`)
- `src/commands/tdd/scaffold.ts`: 11 markers (template/example)
- `src/agents/code-generation-language.ts`: 6 markers (template/example)
- `src/self-improvement/phase4-code-generation.ts`: 6 markers (template/example)
- `docs/quality/self-improvement-summary.md`: 5 markers (template/example)
- `spec/bdd/steps/template.steps.ts`: 5 markers (template/example)
- `docs/templates/spec-kit/property-template.md`: 3 markers (template/example)
- `scripts/maintenance/extract-todo-markers.mjs`: 3 markers (template/example)
- `tests/unit/scripts/extract-todo-markers.test.ts`: 3 markers (template/example)
- `docs/testing/integration-runtime-helpers.md`: 2 markers (template/example)
- `scripts/codex/generate-contract-tests.mjs`: 2 markers (template/example)
- `src/agents/test-generation-agent.ts`: 2 markers (template/example)
- `src/self-improvement/phase5-verification-final.ts`: 2 markers (template/example)

## Next actions
- #2329, #2330 を優先実装し、完了時に該当マーカーを削除またはIssue参照付きに更新する。
- `planned` 項目はCLI/Conformance/Public APIの3系統に分割して段階処理する。
- TODO抽出コマンド実行時に本バックログを更新し、Issue #2322 のチェックリストを同期する。
