# Formal Tools Setup

This guide outlines local setup for formal verification tools used alongside AE-Framework. All steps are optional; CI remains label-gated.

Supported tools
- TLA+ (TLC)
- Apalache (SMT/BMC + inductive invariants)
- SMT solvers: Z3, cvc5
- Kani (Rust bounded model checking)

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
  - (cargo plugin installedの場合) `cargo kani --version`

Notes
- Tools are not required to work with AE-Framework; they enhance the formal workflow when present.
- Use `Formal Verify` workflow with `run-formal` label or manual dispatch to run CI stubs. Engines will be wired incrementally.
