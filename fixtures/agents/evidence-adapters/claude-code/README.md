# Claude Code task fixture

Raw fixture: `../claude-code-task-output.json`

## Producer boundary

Claude Code output is producer-side task evidence. Repository validation, reviewer disposition, and generated ae-framework artifacts remain authoritative.

## Expected normalized routing

- `ae-handoff/v1` for continuation state and unresolved decisions.
- `hook-feedback/v1` for missing validation or blockers.
- `change-package/v2` for changed-file scope after maintainer inspection.
- Optional `claim-evidence-manifest/v1` when claims, waivers, or evidence are present.

Do not create Claude-specific assurance vocabulary.
