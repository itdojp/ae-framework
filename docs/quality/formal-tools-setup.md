# Formal Tools Setup

This guide outlines local setup for formal verification tools used alongside AE-Framework. All steps are optional; CI remains label-gated.

Supported tools
- TLA+ (TLC)
- Apalache (SMT/BMC + inductive invariants)
- Alloy (Alloy Analyzer / Alloy 6 CLI)
- SMT solvers: Z3, cvc5
- Kani (Rust bounded model checking)
- SPIN (Promela model checking)
- CSP (CSPM checks via `cspx` or configured backend)
- Lean4 (theorem proving / typechecking via lake)

Quick checks
- Run `pnpm run tools:formal:check` to see which tools are available on your machine.

TLA+ (TLC)
- Install Java 11+ (OpenJDK recommended)
- Download tla2tools.jar from the TLA+ releases
- Usage:
  - `java -cp /path/to/tla2tools.jar tlc2.TLC DomainSpec.tla`
- Optional env:
  - `TLA_TOOLS_JAR=/path/to/tla2tools.jar`

Apalache
- Install via package manager or releases: https://github.com/apalache-mc/apalache
- Verify:
  - `apalache-mc version`
- Example:
  - `apalache-mc check --inv=Invariant spec/tla/DomainSpec.tla`

Alloy
- Download Alloy 6 jar (example):
  - `curl -L -o alloy.jar https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/org.alloytools.alloy.dist.jar`
- Verify (CLI):
  - `java -jar alloy.jar help`
- Run (CLI exec):
  - `ALLOY_JAR=$PWD/alloy.jar ALLOY_RUN_CMD='java -jar $ALLOY_JAR exec -q -o - -f {file}' pnpm run verify:model`

Z3 / cvc5
- Install via package manager or releases
- Verify:
  - `z3 --version`
  - `cvc5 --version`

Kani
- Install via releases or cargo (see https://github.com/model-checking/kani)
- Example (Linux x86_64, prebuilt):
  - `curl -L -o kani.tar.gz https://github.com/model-checking/kani/releases/download/kani-0.67.0/kani-0.67.0-x86_64-unknown-linux-gnu.tar.gz`
  - `tar -xzf kani.tar.gz`
  - `export PATH="$PWD/kani-0.67.0/bin:$PATH"`
- Verify:
  - `kani-driver --version`
  - (if the cargo plugin is installed) `cargo kani --version`

SPIN
- Install via package manager (Linux example):
  - `sudo apt-get update && sudo apt-get install -y spin gcc`
- Verify:
  - `spin -V`
  - `gcc --version`

CSP
- CI is wired as **non-blocking**: it always produces `csp-summary.json` and does not fail the workflow by default.
- Recommended backend: `cspx` (OSS, Apache-2.0) — CI-first CSPM checks with JSON output.
  - Install (example: pinned to a commit for reproducibility):
    - `cargo install --git https://github.com/itdojp/cspx --rev 4e7c6ac57b88369009517cb8b797e1d526e4b1e4 --locked cspx`
  - Verify:
    - `cspx --version`
  - Run (sample within currently supported subset):
    - `pnpm run verify:csp -- --file spec/csp/cspx-smoke.cspm --mode typecheck`
- Fallback backends (best-effort): `CSP_RUN_CMD` → `cspx` → `refines` (FDR) → `cspmchecker`.
  - `CSP_RUN_CMD` supports `{file}` placeholder (absolute file path).
  - Example (placeholder):
    - `CSP_RUN_CMD='echo Running CSP tool on {file}' pnpm run verify:csp -- --file spec/csp/sample.cspm`

Lean4 (elan + lake)
- Install `elan` (recommended):
  - `curl -L -sS https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y`
  - `export PATH="$HOME/.elan/bin:$PATH"`
- Verify:
  - `elan --version`
  - `lake --version`
- Build (project under `spec/lean/`):
  - `pnpm run verify:lean`

Notes
- Tools are not required to work with AE-Framework; they enhance the formal workflow when present.
- Use `Formal Verify` workflow with `run-formal` label or manual dispatch to run CI stubs. Engines will be wired incrementally.
