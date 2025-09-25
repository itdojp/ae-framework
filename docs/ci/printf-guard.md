# printf Guard for GitHub Outputs/Env

This repository enforces a printf policy when appending to GitHub special files:

- $GITHUB_OUTPUT (step outputs)
- $GITHUB_ENV (environment variables)

## Policy

At a glance:
- Use `printf` (no `echo` / `tee -a` / `::set-output`)
- Quote target files: `>> "$GITHUB_OUTPUT"` / `>> "$GITHUB_ENV"`
- Include a trailing newline in the format (prefer `"%s\n"`)
- `${GITHUB_OUTPUT}` / `${GITHUB_ENV}` are accepted
- Multi-line values: emit delimiter + lines with separate `printf` appends

- Do not use `echo` to append. Use `printf` with a trailing newline.
- Always quote the target file.
- Grouped blocks are allowed for multiple appends.

### Newline requirement

- Include a trailing newline in the printf format. Prefer:

```bash
printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"
```

### Allowed

```bash
printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"
printf "%s\n" "NAME=value" >> "$GITHUB_ENV"
printf "%s\n" "also_good=true" >> "${GITHUB_OUTPUT}"

{
  printf "%s\n" "one=1"
  printf "%s\n" "two=2"
} >> "$GITHUB_OUTPUT"

# Multi-line outputs using delimiter pattern
printf "%s\n" "key<<EOF" >> "$GITHUB_OUTPUT"
printf "%s\n" "line1" >> "$GITHUB_OUTPUT"
printf "%s\n" "line2" >> "$GITHUB_OUTPUT"
printf "%s\n" "EOF" >> "$GITHUB_OUTPUT"
```

### Forbidden

```bash
echo "key=value" >> $GITHUB_OUTPUT          # ❌ echo is not allowed
printf "%s\n" "key=value" >> $GITHUB_OUTPUT  # ❌ unquoted target
echo "key=value" | tee -a "$GITHUB_OUTPUT"   # ❌ tee -a is not allowed (use printf)
echo "::set-output name=val::deprecated"        # ❌ deprecated; use printf >> "$GITHUB_OUTPUT"
cat <<EOF >> "$GITHUB_OUTPUT"                 # ❌ here-doc to special files not allowed (use printf)
key=value
EOF
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

## Troubleshooting

- CI shows "Use printf with quoted target (no echo)"
  - Replace `echo "key=value" >> $GITHUB_OUTPUT` with `printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"`
- CI shows "Quote $GITHUB_OUTPUT/$GITHUB_ENV in redirection"
  - Ensure the target is quoted: `>> "$GITHUB_OUTPUT"` / `>> "$GITHUB_ENV"` (or `${...}` forms)
- CI shows "Use printf for appends to special files"
  - Do not use `tee -a`, `cat file >> "$GITHUB_OUTPUT"`, etc.; use `printf` as in the recipes
- CI shows "Include trailing newline in printf format"
  - Prefer `printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"` over `printf "%s" ...`
- CI shows "Deprecated ::set-output"
  - Replace with `printf` to `$GITHUB_OUTPUT` and consume via `${{ steps.<id>.outputs.<name> }}`

## CI Output

- When violations are found, the guard emits GitHub error annotations with file/line for quick navigation.
- The echo→printf suggestion tool groups its hints in CI logs (`::group:: ... ::endgroup::`) for readability.
