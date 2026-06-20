# Example exported Codex Issue task

Issue: https://github.com/itdojp/ae-framework/issues/0000
Repository: itdojp/ae-framework
Issue number: 0000
Exported at: 2026-06-20T00:00:00.000Z

Local task file: do not stage or commit this file. Keep it under `.codex-local/tasks/`.

## Context Pack preflight

- Read `AGENTS.md`.
- Read `docs/spec/context-pack.md` and `spec/context-pack/boundary-map.json`.
- Identify the Context Pack `objects`, `morphisms`, `diagrams`, `acceptance_tests`, and existing tests relevant to the Issue target files.
- If the requested change conflicts with Context Pack constraints or the boundary map, stop before implementation and record `Context Pack conflict: found` with the conflicting IDs/paths in the PR or Issue comment.
- If no conflict is found, record `Context Pack conflict: none` in the PR body.
- Do not promote routine changes to MBT, property, or formal lanes unless the Issue, risk label, assurance profile, or critical-core boundary requires it.

## Issue body

Paste or export the GitHub Issue body here. Keep the Issue URL above so the PR
can cite the source task without committing local `.codex-local/tasks/` files.
