# Codex CLI local task fixture

Raw fixture: `../codex-cli-task-output.json`

## Producer boundary

Codex CLI is an evidence producer. Its local task summary, command transcript, and continuation notes are untrusted until the maintainer verifies the diff and schema-backed artifacts.

## Expected normalized routing

- `change-package/v2` for changed-file scope and reviewability.
- `claim-evidence-manifest/v1` when task output mentions claims or evidence.
- `producer-normalization-summary/v1` for report-only raw-signal routing.
- `ae-handoff/v1` / `hook-feedback/v1` for continuation blockers and next actions.

Do not treat a Codex completion message as approval, proof, or policy pass.
