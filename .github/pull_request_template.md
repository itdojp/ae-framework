<!-- Short and focused PRs are preferred. Link issues like Refs #NNN. -->

## Summary
-

## Checklist
- [ ] Workflows use `printf` with quoted `$GITHUB_OUTPUT`/`$GITHUB_ENV` (no `echo`/`tee -a`/`::set-output`)
- [ ] `printf` includes a trailing newline (prefer `"%s\n"`)
- [ ] `pnpm lint:workflows` passes locally (guard + actionlint via Docker if available)
- [ ] (Optional) `pnpm lint:workflows:nodocker` used (guard + self-test only) when Docker unavailable
 - [ ] (Optional) `pnpm ci:test:guard:all` passes (guard + disable tests)
 - [ ] (Optional) Run `pnpm ci:guard:suggest` to see echo→printf conversion hints (non-destructive)
 - [ ] (Optional) Policy tests pass: `pnpm ci:test:policy:all` (guard + suggest)
- [ ] Scope limited to the stated objective

## Notes
- Policy & examples: `docs/ci/printf-guard.md`
- CI runs `workflow-lint.yml` (guard self-test + `rhysd/actionlint@v1.7.1`)
