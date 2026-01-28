# CLI Entry Migration Guide (Issue #1006)

This guide documents the migration from legacy `pnpm run` scripts to the consolidated runner entry points and the `ae entry` command.

## Summary
- Consolidated runners live under `scripts/<category>/run.mjs`.
- The `ae entry <category>` command routes to those runners.
- Legacy scripts remain available via alias mapping and emit deprecation warnings.

## What changed
### New entry runners
Each category has a unified entry script with a consistent interface:

```
node scripts/<category>/run.mjs --profile <name> [--list] [--dry-run]
```

### New CLI routing
Run the same entry from the CLI without knowing the script path:

```
ae entry <category> --profile <name> [--list] [--dry-run] [--root <path>]
```

Use `--root` when invoking from outside the repository. The command switches its working directory to the given root before executing the runner.

### Legacy aliases (still supported)
Legacy scripts are wired through `scripts/admin/run-script-alias.mjs` and configured in:

- `scripts/admin/script-alias-map.json`

The policy is to keep legacy names for two releases while emitting warnings.

## Quick mapping (legacy -> entry)
| Legacy script | Replacement |
| --- | --- |
| `test:ci` | `ae entry test --profile ci` |
| `test:ci:lite` | `ae entry test --profile ci-lite` |
| `test:ci:extended` | `ae entry test --profile ci-extended` |
| `quality:run:all` | `ae entry quality --profile all` |
| `quality:gates` | `ae entry quality --profile gates` |
| `verify:lite` | `ae entry verify --profile lite` |
| `verify:conformance` | `ae entry verify --profile conformance` |
| `flake:detect` | `ae entry flake --profile detect` |
| `flake:detect:quick` | `ae entry flake --profile quick` |
| `security:integrated:quick` | `ae entry security --profile quick` |

## Examples
```bash
# List profiles for a category
$ ae entry test --list

# Dry-run to see the resolved commands
$ ae entry verify --dry-run --profile lite

# Run from another directory
$ ae entry test --profile ci-lite --root /path/to/repo
```

## Troubleshooting
- If you see `[script-alias]` warnings, switch to the `ae entry` command shown in the mapping table.
- If a runner script is missing, confirm you are running from the repository root or pass `--root`.
