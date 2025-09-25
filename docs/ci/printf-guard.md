# printf Guard for GitHub Outputs/Env

This repository enforces a printf policy when appending to GitHub special files:

- $GITHUB_OUTPUT (step outputs)
- $GITHUB_ENV (environment variables)

## Policy

- Do not use `echo` to append. Use `printf` with a trailing newline.
- Always quote the target file.
- Grouped blocks are allowed for multiple appends.

### Allowed

```bash
printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"
printf "%s\n" "NAME=value" >> "$GITHUB_ENV"

{
  printf "%s\n" "one=1"
  printf "%s\n" "two=2"
} >> "$GITHUB_OUTPUT"
```

### Forbidden

```bash
echo "key=value" >> $GITHUB_OUTPUT          # ❌ echo is not allowed
printf "%s\n" "key=value" >> $GITHUB_OUTPUT  # ❌ unquoted target
echo "key=value" | tee -a "$GITHUB_OUTPUT"   # ❌ tee -a is not allowed (use printf)
```

## CI Enforcement

- The guard runs in `workflow-lint.yml` alongside `rhysd/actionlint@v1.7.1`.
- Guard script: `scripts/ci/guard-github-outputs.sh`
  - Blocks `echo >> $GITHUB_OUTPUT/$GITHUB_ENV`
  - Requires quoted targets: `>> "$GITHUB_OUTPUT"` / `>> "$GITHUB_ENV"`
  - Requires `printf` for single-line appends
  - Allows grouped printf blocks `{ ... } >> "$GITHUB_OUTPUT"`
  - Ignores commented YAML lines

## Local Usage

- Run guard + actionlint:

```bash
pnpm lint:workflows
```

- Or run guard only:

```bash
bash scripts/ci/guard-github-outputs.sh
```

### Temporary Disable (debug only)

Set `PRINTF_GUARD_DISABLE=1` to skip guard checks (e.g., local debugging). Do not use in CI except in emergencies.

## Rationale

- `printf` provides predictable formatting and explicit newlines.
- Quoting targets prevents word-splitting or brace expansion issues.
- Grouped blocks reduce duplication and keep steps concise.
