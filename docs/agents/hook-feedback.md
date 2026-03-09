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

- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/ci/harness-health.json`
- `artifacts/change-package/change-package.json`
- `artifacts/context-pack/context-pack-suggestions.json`（存在時のみ）

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
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json \
  --context-pack-suggestions artifacts/context-pack/context-pack-suggestions.json
```

`context-pack-suggestions` が無い場合は省略できます。

## Claude Code hook command example

Claude Code 側で post-verify / post-check 相当の command hook を設定できる場合は、次のコマンドを実行対象にします。

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json
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
- `status=blocked` / `warn` の場合は `blockingReasons[]` を必須とします。
- この adapter は既存 artifact を再構成するだけで、元の gate 判定を上書きしません。
