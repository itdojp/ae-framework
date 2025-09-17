# Adapter CI Examples

This note consolidates adapter-related CI snippets and where to place artifacts.

- Upload  for adapters to be summarized in PR comments.
- Keep XML/JUnit raw files as artifacts, but aggregate from JSON.
- See: docs/templates/ci/testing-ddd-scripts.snippet.yml

Minimal snippet:

```yaml
name: adapters-quick
on: [pull_request]
jobs:
  adapters:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with: { node-version: '20' }
      - run: pnpm install --frozen-lockfile || pnpm install
      - name: Run BDD lint (non-blocking)
        run: node scripts/bdd/lint.mjs || true
      - name: BDD → LTL suggestions (report-only)
        run: pnpm -s run bdd:suggest || true
      - name: Aggregate adapter artifacts
        run: pnpm -s run artifacts:aggregate || true
      - name: Render PR summary (digest)
        env:
          SUMMARY_MODE: digest
          SUMMARY_LANG: ${{ contains(github.event.pull_request.labels.*.name, 'lang:ja') && 'ja' || 'en' }}
        run: node scripts/summary/render-pr-summary.mjs || true
```

