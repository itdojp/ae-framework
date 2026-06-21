# GitHub Copilot PR review / agent fixture

Raw fixture: `../copilot-pr-review-output.json`

## Producer boundary

Copilot review bodies, inline comments, suggestions, and thread state are review input. They become control-plane evidence only through recorded disposition, thread resolution, and required checks.

## Expected normalized routing

- `policy-decision/v1` for resolved/unresolved review gate state.
- Optional `change-package/v2` for review-driven follow-up commits.
- `hook-feedback/v1` when unresolved AI review threads must be returned as blockers.

Unresolved AI review threads remain blockers; non-actionable comments need an explicit disposition.
