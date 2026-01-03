# Issue 1006: Module Structure Classification (Phase 1.5 draft)

## Snapshot
- Commit: 988bef51
- Input: docs/notes/issue-1006-structure-inventory.md

## Classification (draft, by intent)

### Domain and core building blocks
- core
- domain
- types
- schemas
- utils

### Runtime and orchestration
- runtime
- runner
- services
- infra

### Interfaces and adapters
- api
- web-api
- routes
- cli
- commands
- mcp-server

### Verification and quality
- quality
- contracts
- conformance
- testing
- integration
- benchmark
- analysis
- optimization
- cegis

### Agent and model layer
- agents
- models
- inference
- providers
- engines
- generators
- codegen
- self-improvement

### Cross-cutting concerns
- security
- resilience
- telemetry
- health

### UI
- ui

### Other / to classify further
- lib

## Overlap candidates (to verify)
- api / routes / web-api: possible duplication in HTTP entry points
- cli / commands / runner: execution entry points and orchestration are split
- integration / testing: shared helpers vs suite definitions may be spread
- models / providers / inference / engines: boundary between model IO and orchestration is unclear
- quality / analysis / benchmark / optimization: reporting vs execution responsibilities overlap

## Next steps
- Validate the above mapping by checking ownership of key modules and their public entry points.
- Propose a stable taxonomy (and folder naming) for the core paths.
- Identify 1-2 low-risk move candidates for Phase 2 refactors.
