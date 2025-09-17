# LTL Suggestions (report-only)

- Generator: `scripts/bdd/ltl-suggest.mjs`
- Outputs:
  - `artifacts/bdd/scenarios.json` — `{ title, criteriaCount }` (PR summary line)
  - `artifacts/properties/ltl-suggestions.json` — `{ count, items[] }` (reference)

CI snippet (warn when count > 0):

```yaml
- name: LTL suggestions (warn-only)
  run: |
    if [ -f artifacts/properties/ltl-suggestions.json ]; then \
      cnt=$(jq -r '.count // 0' artifacts/properties/ltl-suggestions.json 2>/dev/null || echo 0); \
      printf "LTL suggestions: %s\n" "$cnt"; \
      if [ "$cnt" -gt 0 ]; then printf "::warning::LTL suggestions present (%s)\n" "$cnt"; fi; \
    fi
```

Notes:
- The generator is heuristic and report-only; human review is expected before promoting to formal properties.
- Keep it non-blocking (warn-only) by default, and gate via labels when needed.

