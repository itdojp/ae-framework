# Echo → printf Recipes (GITHUB_OUTPUT / GITHUB_ENV)

Short, copy‑pasteable patterns to convert echo‑based appends to the policy‑compliant printf form.

## Single key/value

```bash
# Before (NG)
echo "key=value" >> $GITHUB_OUTPUT

# After (OK)
printf "%s\n" "key=value" >> "$GITHUB_OUTPUT"
```

## Multiple keys (grouped)

```bash
{
  printf "%s\n" "one=1"
  printf "%s\n" "two=2"
} >> "$GITHUB_OUTPUT"
```

## Using ${…} form

```bash
printf "%s\n" "NAME=value" >> "${GITHUB_ENV}"
printf "%s\n" "also_good=true" >> "${GITHUB_OUTPUT}"
```

## Multi‑line output (with delimiter)

```bash
# Emits:
# key<<EOF\nline1\nline2\nEOF
printf "%s\n" "key<<EOF" >> "$GITHUB_OUTPUT"
printf "%s\n" "line1"    >> "$GITHUB_OUTPUT"
printf "%s\n" "line2"    >> "$GITHUB_OUTPUT"
printf "%s\n" "EOF"      >> "$GITHUB_OUTPUT"
```

## JSON values (quoted)

```bash
val=$(jq -rc '.field' input.json)
printf "%s\n" "json=$val" >> "$GITHUB_OUTPUT"
```

## Environment variables

```bash
printf "%s\n" "FOO=$FOO" >> "$GITHUB_ENV"
```

## Forbidden patterns (replace with the above)

```bash
# NG: echo, unquoted targets, tee -a, ::set-output, here-doc redirects
# echo "key=value" >> $GITHUB_OUTPUT
# printf "%s" "NO_NL=true" >> "$GITHUB_OUTPUT"
# echo "key=value" | tee -a "$GITHUB_OUTPUT"
# echo "::set-output name=val::deprecated"
# cat <<EOF >> "$GITHUB_OUTPUT"; cat file >> "$GITHUB_OUTPUT"
```

See also:
- docs/ci/printf-guard.md (policy, allowed/forbidden, CI/local usage)
- docs/ci-policy.md (project CI policy and guard integration)
