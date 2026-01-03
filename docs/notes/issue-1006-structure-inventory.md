# Issue 1006: Module Structure Inventory (Phase 1)

## Snapshot
- Commit: 988bef51
- src/ top-level directories: 38
- src/ top-level files: 3 (cli.ts, index.ts, server.ts)
- packages/: 4

## src/ top-level directories
- agents
- analysis
- api
- benchmark
- cegis
- cli
- codegen
- commands
- conformance
- contracts
- core
- domain
- engines
- generators
- health
- inference
- infra
- integration
- lib
- mcp-server
- models
- optimization
- providers
- quality
- resilience
- routes
- runner
- runtime
- schemas
- security
- self-improvement
- services
- telemetry
- testing
- types
- ui
- utils
- web-api

## packages/
- design-tokens
- envelope
- spec-compiler
- ui

## Next (Phase 1.5 draft)
- Classify modules by intent (domain/core/runtime/infra/integration/tooling) and identify overlaps or move candidates.
- Combine with docs/notes/issue-1006-script-inventory.md and reflect Phase 1 findings in Issue #1006.
