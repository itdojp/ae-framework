# Tests-First Intent Mode

This guide describes the **tests-first** workflow proposed in #1067: generate tests immediately after intent capture, then **rank code candidates** by how well they satisfy those tests.

## Goals

- Make `ae tests:suggest` the default step after intent capture.
- Use `ae code:rank-by-tests` to select the best code candidate based on test outcomes.
- Provide starter prompts for common domains to reduce prompt variance.

## Workflow

1. **Intent**: Capture user requirements in natural language.
2. **Tests**: Generate tests that represent the intent.
3. **Candidates**: Produce multiple code candidates.
4. **Rank**: Run tests against each candidate and score them.
5. **Select**: Pick the top-ranked candidate and continue the pipeline.

## Ranking Heuristics (initial proposal)

```
score = pass_rate
      - flake_penalty
      - runtime_penalty

pass_rate       = passed_tests / total_tests
flake_penalty   = flake_count * 0.02
runtime_penalty = min(runtime_ms / 60000, 0.2)
```

Notes:
- Penalize flaky tests explicitly to avoid unstable selections.
- Cap runtime penalty to avoid over-penalizing complex suites.
- Adjust weights per project constraints (CI vs local).

## Templates

Starter prompts live in `templates/prompts/`:
- `templates/prompts/tests-first-http-api.md`
- `templates/prompts/tests-first-queue.md`
- `templates/prompts/tests-first-auth.md`
- `templates/prompts/tests-first-math.md`

Use these as baseline prompts for test generation to keep outputs consistent across runs.

## Next Steps

- Wire `ae tests:suggest` as the default route in the 6-phase docs and CLI.
- Implement `ae code:rank-by-tests` using the scoring heuristic above.
- Add optional `--autofix` flow to patch failing tests and re-rank.
