#!/usr/bin/env bash
set -euo pipefail

pnpm vitest run tests/property --reporter dot
pnpm vitest run tests/unit/api/server.test.ts --reporter dot
pnpm vitest run tests/unit/utils/enhanced-state-manager.test.ts --reporter dot
pnpm vitest run tests/resilience/integration.test.ts --reporter dot
