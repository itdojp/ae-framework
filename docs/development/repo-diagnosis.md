---
docRole: ssot
lastVerified: '2026-03-11'
owner: development-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Repository Diagnosis Report

> 🌍 Language / 言語: English | 日本語

## Environment Detection
- **Node.js**: v20.19.4 ✅
- **Package Manager**: npm (package-lock.json detected)
- **Module Type**: ESM ("type": "module")
- **Test Runner**: vitest
- **Build System**: TypeScript (tsc)

## Dependencies Status
- **Existing**: zod ✅
- **Required for P0**: 
  - ❌ execa (for subprocess execution)
  - ❌ micromatch (for glob pattern matching)  
  - ❌ tinybench (for benchmark execution)
  - ❌ cac (for CLI argument parsing)

## Directory Structure
- `src/` - Source code directory exists
- `src/cli/` - CLI directory exists
- `dist/` - Build output directory (via tsc)

## Current CLI Commands
- `ae-framework` (main entry)
- `ae-phase`, `ae-approve`, `ae-slash`, `ae-ui`, `ae-sbom`, `ae-resilience`, `ae-benchmark`

## P0 Implementation Strategy
1. Add missing dependencies
2. Create unified `ae` command structure
3. Implement TDD guard with scoped control
4. Add deterministic seed support
5. Replace existing benchmark with tinybench
6. Add QA coverage threshold enforcement
