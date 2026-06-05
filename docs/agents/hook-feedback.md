---
docRole: derived
canonicalSource:
- docs/ci/pr-automation.md
- docs/integrations/CODEX-CONTINUATION-CONTRACT.md
lastVerified: '2026-03-31'
---

# Hook Feedback Adapter

> 🌍 Language / 言語: English | 日本語

---

## English

This is the minimal adapter that normalizes existing CI and evidence artifacts into short feedback that Claude Code and Codex can feed back into the next continuation step without manual reshaping.

### Standard outputs

- JSON: `artifacts/agents/hook-feedback.json`
- Markdown: `artifacts/agents/hook-feedback.md`
- schema: `schema/hook-feedback.schema.json`
- builder: `node scripts/agents/build-hook-feedback.mjs`
- `PR Maintenance` (`.github/workflows/pr-ci-status-comment.yml`) generates the adapter output in report-only mode when it can download the `verify-lite-report` artifact for the same head SHA

### Inputs

- required: `artifacts/verify-lite/verify-lite-run-summary.json`
- optional: `artifacts/ci/harness-health.json`
- optional: `artifacts/change-package/change-package.json`
- present-only: `artifacts/context-pack/context-pack-suggestions.json`
- present-only: `artifacts/assurance/assurance-summary.json`
- present-only: `artifacts/e2e/ui-e2e-summary.json`

### Contract fields

- `status`: `ok | warn | blocked`
- `blockingReasons[]`: short list of blocking or warning reasons
- `nextActions[]`: the next actions the operator or agent should take as-is
- `reproCommands[]`: local reproduction commands
- `evidence[]`: artifacts to inspect next
- `source`: resolved input artifact paths

### Minimal usage

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
```

The builder still runs when `harness-health`, `change-package`, `context-pack-suggestions`, `assurance-summary`, or `ui-e2e-summary` are missing. Missing artifacts are reflected through `blockingReasons`, `nextActions`, `evidence.present=false`, and `source.*Path=null`.

### Optional inputs example

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json \
  --context-pack-suggestions artifacts/context-pack/context-pack-suggestions.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --ui-e2e-summary artifacts/e2e/ui-e2e-summary.json
```

### Claude Code hook command example

If Claude Code can run a post-verify or post-check command hook, use the builder directly:

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
```

For the next assistant input, attach `artifacts/agents/hook-feedback.md` as-is. If the hook consumes structured data, prefer `artifacts/agents/hook-feedback.json`.

### Codex continuation usage

In Codex continuation flows, add `artifacts/agents/hook-feedback.json` as a preprocessing artifact and prioritize these fields:

1. `status`
2. `blockingReasons[]`
3. `nextActions[]`
4. `reproCommands[]`

Minimal resume command:

```bash
jq '{status, blockingReasons, nextActions, reproCommands}' artifacts/agents/hook-feedback.json
```

### Notes

- `reproCommands[]` always emits at least one item. When the inputs contain no explicit command, the fallback is `pnpm run verify:lite`.
- Missing `harness-health` or `change-package` upgrades the output to `status=warn` and adds generation commands to `nextActions` and `reproCommands`.
- The `summarize` job in `pr-ci-status-comment.yml` only auto-builds hook feedback when it can download the latest successful `verify-lite-report` artifact from `verify-lite.yml`.
- When `assurance-summary` exists, `warningClaims`, `missingLanes`, `missingEvidenceKinds`, `unlinkedCounterexamples`, and `openCounterexamples` are propagated into `blockingReasons` and `nextActions`.
- When `ui-e2e-summary` exists, the failed scenario IDs and status are propagated into `blockingReasons` and `nextActions`.
- `status=blocked` or `status=warn` requires `blockingReasons[]`.
- This adapter only restructures existing artifacts. It does not override the original gate result.

## 日本語

既存の CI / evidence artifact を、Claude Code や Codex が次の continuation step にそのまま再入力できる短い feedback に正規化する最小 adapter です。

### Standard outputs

- JSON: `artifacts/agents/hook-feedback.json`
- Markdown: `artifacts/agents/hook-feedback.md`
- schema: `schema/hook-feedback.schema.json`
- builder: `node scripts/agents/build-hook-feedback.mjs`
- `PR Maintenance`（`.github/workflows/pr-ci-status-comment.yml`）は、同一 head SHA の `verify-lite-report` artifact を取得できた場合に report-only で自動生成します

### Inputs

- required: `artifacts/verify-lite/verify-lite-run-summary.json`
- optional: `artifacts/ci/harness-health.json`
- optional: `artifacts/change-package/change-package.json`
- present-only: `artifacts/context-pack/context-pack-suggestions.json`
- present-only: `artifacts/assurance/assurance-summary.json`
- present-only: `artifacts/e2e/ui-e2e-summary.json`

### Contract fields

- `status`: `ok | warn | blocked`
- `blockingReasons[]`: 停止理由または警告理由の短い列挙
- `nextActions[]`: operator または agent がそのまま次に実行すべき作業
- `reproCommands[]`: ローカル再現コマンド
- `evidence[]`: 次に確認すべき artifact
- `source`: 解決済みの入力 artifact path

### Minimal usage

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
```

`harness-health`、`change-package`、`context-pack-suggestions`、`assurance-summary`、`ui-e2e-summary` が欠けていても builder は継続します。不足は `blockingReasons`、`nextActions`、`evidence.present=false`、`source.*Path=null` に反映されます。

### Optional inputs example

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --harness-health artifacts/ci/harness-health.json \
  --change-package artifacts/change-package/change-package.json \
  --context-pack-suggestions artifacts/context-pack/context-pack-suggestions.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --ui-e2e-summary artifacts/e2e/ui-e2e-summary.json
```

### Claude Code hook command example

Claude Code 側で post-verify / post-check 相当の command hook を実行できる場合は、builder をそのまま呼び出します。

```bash
pnpm run hook-feedback:build \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
```

次の assistant 入力には `artifacts/agents/hook-feedback.md` をそのまま添付すれば足ります。構造化データを扱う hook では `artifacts/agents/hook-feedback.json` を優先します。

### Codex continuation usage

Codex continuation flow では `artifacts/agents/hook-feedback.json` を前処理 artifact として追加し、次のフィールドを優先的に使います。

1. `status`
2. `blockingReasons[]`
3. `nextActions[]`
4. `reproCommands[]`

最小の再開コマンド:

```bash
jq '{status, blockingReasons, nextActions, reproCommands}' artifacts/agents/hook-feedback.json
```

### Notes

- `reproCommands[]` は最低 1 件出力されます。入力に明示的な command が無い場合の fallback は `pnpm run verify:lite` です。
- `harness-health` または `change-package` が無い場合は `status=warn` となり、生成コマンドを `nextActions` と `reproCommands` に追加します。
- `pr-ci-status-comment.yml` の `summarize` job は、`verify-lite.yml` の最新 successful `verify-lite-report` artifact を取得できた場合だけ hook feedback を自動生成します。
- `assurance-summary` がある場合は、`warningClaims`、`missingLanes`、`missingEvidenceKinds`、`unlinkedCounterexamples`、`openCounterexamples` を `blockingReasons` と `nextActions` に反映します。
- `ui-e2e-summary` がある場合は、failed scenario ID と status を `blockingReasons` と `nextActions` に反映します。
- `status=blocked` または `status=warn` の場合は `blockingReasons[]` が必須です。
- この adapter は既存 artifact を再構成するだけで、元の gate 判定を上書きしません。
