## Runtime Contracts from Formal Specs (Week 3)

This document outlines an opt-in path to generate runtime contracts (e.g., Zod schemas, pre/post conditions) and state-machine shells from formal specs.

### Overview

- Contracts are generated alongside code and can be enabled per feature.
- Contracts validate inputs/outputs and pre/post conditions in runtime and can be wired into `verify` as an optional gate.

### How to use (initial)

1) Provide a formal spec (TLA+/Alloy) as a string to `CodeGenerationAgent.generateContractsSkeleton(formalSpec)`.
2) The agent returns files under `src/contracts/` (paths + contents) you can write to disk.
3) Integrate contracts into your service endpoints or use them in tests for runtime checking.

> This is an initial skeleton; future versions will extract specific properties.

