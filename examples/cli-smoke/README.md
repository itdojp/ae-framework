# CLI Smoke Test

Minimal smoke tests to quickly verify that the runner boots and executes.

Two variants are provided:

- CJS + TypeScript (via `tsx` runtime)
  - Runs directly from TypeScript source without building.
  - Command: `node examples/cli-smoke/test-cli.cjs`

- ESM + JavaScript (from built artifacts)
  - Requires a build first.
  - Commands:
    - `pnpm build`
    - `node examples/cli-smoke/test-cli.mjs`

What it does:
- Invokes `main()` from the framework runner to perform a basic boot‑up and exit.
- Intended for quick sanity checks during development.

Notes:
- Ensure dependencies are installed: `pnpm install`
- If `test-cli.mjs` reports missing build artifacts, run `pnpm build` and retry.

