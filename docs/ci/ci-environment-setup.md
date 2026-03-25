---
docRole: ssot
lastVerified: '2026-03-25'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# CI Environment Setup (Quick)

> Language / 言語: English | 日本語

---

## English

Minimal environment notes for reproducing the current CI baseline locally without opening the heavy suites.

### Prerequisites

- Node.js `22.x`
- `pnpm` via Corepack (`corepack enable`)
- Container runtime: Podman or Docker

### Recommended defaults

- Use `.pnpm-store` under the repository root for predictable local caching.
- Use `pnpm run verify:lite` when you need the same lightweight baseline used by the required PR checks.
- Use `pnpm run test:ci:lite` when you want the CI-lite suite without opening the heavier lanes.

### Container runtime notes

- Podman shared-runner setup: `docs/infra/podman-shared-runner.md`
- General container runtime notes: `docs/infra/container-runtime.md`
- Prefer matching the local container runtime to the failing workflow before escalating to CI-only investigation.

### CI gating notes

- Heavy suites are label-gated. See `docs/ci/label-gating.md` for the current opt-in labels and required-check boundaries.
- Treat `docs/ci/stable-profile.md` as the baseline test profile reference for PR verification.
- When reproducing a required-check failure, start from Verify Lite and only escalate to heavier workflows if the baseline is already green.

### Troubleshooting entrypoints

- CI triage runbook: `docs/ci/ci-troubleshooting-guide.md`
- Flaky test triage: `docs/testing/flaky-test-triage.md`
- Stable baseline profile: `docs/ci/stable-profile.md`

## 日本語

重い suite を開かずに、current CI baseline をローカルで再現するための最小環境メモです。

### 前提条件

- Node.js `22.x`
- Corepack 経由の `pnpm`（`corepack enable`）
- Container runtime: Podman または Docker

### 推奨デフォルト

- ローカル cache の挙動を安定させるため、`.pnpm-store` は repository root 配下で運用します。
- required PR checks と同じ軽量 baseline を確認したい場合は `pnpm run verify:lite` を使います。
- heavier lane を開かずに CI-lite suite だけ見たい場合は `pnpm run test:ci:lite` を使います。

### Container runtime メモ

- Podman shared-runner の設定は `docs/infra/podman-shared-runner.md`
- 一般的な container runtime の注意点は `docs/infra/container-runtime.md`
- CI-only 調査へ進む前に、失敗 workflow と同じ runtime をローカルでも揃えることを優先します。

### CI gating メモ

- 重い suite は label-gated 運用です。current opt-in label と required check 境界は `docs/ci/label-gating.md` を参照します。
- PR 検証の baseline test profile は `docs/ci/stable-profile.md` を一次参照とします。
- required check failure を再現する場合は、まず Verify Lite から入り、baseline が green であることを確認してから heavier workflow へ escalation します。

### トラブルシュート入口

- CI triage runbook: `docs/ci/ci-troubleshooting-guide.md`
- flaky test triage: `docs/testing/flaky-test-triage.md`
- stable baseline profile: `docs/ci/stable-profile.md`
