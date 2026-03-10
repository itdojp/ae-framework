---
docRole: derived
canonicalSource:
- docs/ci/pr-automation.md
- docs/integrations/CODEX-CONTINUATION-CONTRACT.md
lastVerified: '2026-03-10'
---

# Hook Feedback Adapter

既存の CI / evidence artifact を、Claude Code / CodeX がそのまま再入力できる短い feedback に正規化するための最小 adapter です。

## Standard outputs

- JSON: `artifacts/agents/hook-feedback.json`
- Markdown: `artifacts/agents/hook-feedback.md`
- Schema: `schema/hook-feedback.schema.json`
- Builder: `node scripts/agents/build-hook-feedback.mjs`

## Inputs

- `artifacts/verify-lite/verify-lite-run-summary.json`（required）
- `artifacts/ci/harness-health.json`（optional）
- `artifacts/change-package/change-package.json`（optional）
- `artifacts/context-pack/context-pack-suggestions.json`（存在時のみ）
- `artifacts/assurance/assurance-summary.json`（存在時のみ）
- `artifacts/e2e/ui-e2e-summary.json`（存在時のみ）

## Contract fields

- `status`: `ok | warn | blocked`
- `blockingReasons[]`: 停止/警告理由の短い列挙
- `nextActions[]`: そのまま次に行う作業の列挙
- `reproCommands[]`: ローカル再現コマンド
- `evidence[]`: 参照すべき artifact
- `source`: 入力 artifact path

## Minimal usage

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
```

`harness-health` / `change-package` / `context-pack-suggestions` / `assurance-summary` / `ui-e2e-summary` が無い場合も builder は継続します。不足 artifact は `blockingReasons`、`nextActions`、`evidence.present=false`、`source.*Path=null` に反映されます。

## Optional inputs example

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json \
  --context-pack-suggestions artifacts/context-pack/context-pack-suggestions.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --ui-e2e-summary artifacts/e2e/ui-e2e-summary.json
```

## Claude Code hook command example

Claude Code 側で post-verify / post-check 相当の command hook を設定できる場合は、次のコマンドを実行対象にします。

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
```

Hook 側は `artifacts/agents/hook-feedback.md` をそのまま次の assistant 入力へ添付すれば十分です。Hook で JSON を扱う場合は `artifacts/agents/hook-feedback.json` を優先します。

## CodeX continuation usage

CodeX 側では `artifacts/agents/hook-feedback.json` を continuation recipe の前処理に追加し、以下を優先的に使います。

1. `status`
2. `blockingReasons[]`
3. `nextActions[]`
4. `reproCommands[]`

最低限の再開手順:

```bash
jq '{status, blockingReasons, nextActions, reproCommands}' artifacts/agents/hook-feedback.json
```

## Notes

- `reproCommands[]` は最低1件出力されます。入力 artifact に command が無い場合は `pnpm run verify:lite` を fallback とします。
- `harness-health` / `change-package` が無い場合は `status=warn` となり、生成コマンドを `nextActions` / `reproCommands` に追加します。
- `assurance-summary` がある場合は `warningClaims` / `missingLanes` / `missingEvidenceKinds` / `unlinkedCounterexamples` / `openCounterexamples` を `blockingReasons` と `nextActions` に反映します。
- `ui-e2e-summary` がある場合は `status` と failed scenario id を `blockingReasons` と `nextActions` に反映します。
- `status=blocked` / `warn` の場合は `blockingReasons[]` を必須とします。
- この adapter は既存 artifact を再構成するだけで、元の gate 判定を上書きしません。
