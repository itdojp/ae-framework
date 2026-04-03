---
docRole: derived
canonicalSource:
- docs/quality/verification-gates.md
- docs/ci/ci-troubleshooting-guide.md
lastVerified: '2026-04-04'
---
# Repository Health Check — 2025-09-05

> 🌍 Language / 言語: English | 日本語

---

## English

### Scope
This report captures the repository health snapshot for Types Gate, Verify, Bench, Flake, Branch Protection, and CI workflow hygiene as of the recorded date.

### Current gates and policies
- PR Verify (`pr-verify.yml`)
  - CodeX quickstart runs in tolerant mode through `CODEX_SKIP_QUALITY=1` and `CODEX_TOLERANT=1`.
  - Summary comments and artifacts are uploaded while the job remains green by design.
- Quality Gates (`quality-gates-centralized.yml`)
  - Trigger only on code changes through `paths` filters over `src/**`, `packages/**`, `apps/**`, `tests/**`, `configs/**`, `scripts/**`, and `types/**`.
- SBOM (`sbom-generation.yml`)
  - Runs when manifests or code change and skips docs-only PRs.
- Security (`security.yml`)
  - Uses `paths-ignore` for docs / markdown to avoid heavy scans on docs-only PRs.
  - Container scan steps are guarded at step level by `hashFiles('docker/Dockerfile')`.
- Parallel Tests (`parallel-test-execution.yml`)
  - The E2E job on PR runs only when the `run-e2e` label is present and always runs on push.
  - Path filters match the quality gates to reduce noise.
- Spec Validation
  - The reusable workflow is exposed through `workflow_call` and referenced by fail-fast pipelines.

### Lint and hygiene
- `actionlint`: all workflows passed local `actionlint v1.7.1` when this report was produced.
- Reusable workflows expose `workflow_call` and optional inputs.

### Types and tests
- Strict types mode env is available through `AE_TYPES_STRICT=1`.
- Stable CI test profile is available with `pnpm run test:ci:stable` and excludes heavy system-integration suites. See `docs/ci/stable-profile.md`.

### Suggested branch protection baseline
- Require: `actionlint`, PR Verify, minimal Quality Gates, SBOM for manifest changes, Security fast lanes, and Spec Validation when spec-related paths are in scope.
- Optional: the label-gated E2E job does not need to be a required status.

### Follow-ups recorded in this report
- Document additional stable-profile exclusions as flaky suites are identified.
- Track CI duration metrics and refine path filters accordingly.

## 日本語

### 対象範囲
このレポートは、記録時点における Types Gate、Verify、Bench、Flake、Branch Protection、および CI workflow hygiene のリポジトリ健全性スナップショットをまとめたものです。

### 現行のゲートとポリシー
- PR Verify (`pr-verify.yml`)
  - CodeX quickstart は `CODEX_SKIP_QUALITY=1` と `CODEX_TOLERANT=1` による tolerant mode で動作します。
  - summary comment と artifact は upload されますが、job は設計上 green のままです。
- Quality Gates (`quality-gates-centralized.yml`)
  - `src/**`, `packages/**`, `apps/**`, `tests/**`, `configs/**`, `scripts/**`, `types/**` に対する `paths` filter により、code change 時のみ起動します。
- SBOM (`sbom-generation.yml`)
  - manifest または code change 時に起動し、docs-only PR は対象外です。
- Security (`security.yml`)
  - docs / markdown のみの PR で重い scan を避けるため `paths-ignore` を使います。
  - container scan step は `hashFiles('docker/Dockerfile')` により step level で guard されています。
- Parallel Tests (`parallel-test-execution.yml`)
  - PR 上の E2E job は `run-e2e` label がある場合にのみ起動し、push では常時実行されます。
  - path filter は quality gates と同一で、noise を抑える構成です。
- Spec Validation
  - reusable workflow は `workflow_call` を公開し、fail-fast pipeline から参照されます。

### Lint と hygiene
- `actionlint`: このレポート作成時点で、すべての workflow がローカル `actionlint v1.7.1` を通過しています。
- reusable workflow は `workflow_call` と optional input を公開しています。

### Types と tests
- strict types mode 用の env として `AE_TYPES_STRICT=1` が利用可能です。
- stable CI test profile は `pnpm run test:ci:stable` で利用でき、重い system-integration suite を除外します。`docs/ci/stable-profile.md` を参照してください。

### 推奨 branch protection baseline
- required にする対象: `actionlint`、PR Verify、minimal Quality Gates、manifest change 向け SBOM、Security fast lane、spec 関連 path が対象の場合の Spec Validation。
- optional にする対象: label-gated E2E job は required status にする必要はありません。

### このレポートで記録する follow-up
- flaky suite が判明したら stable profile から除外する対象を追加で文書化する。
- CI duration metric を追跡し、path filter を継続的に調整する。
