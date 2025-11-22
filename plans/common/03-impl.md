# ExecPlan: Common / 03-impl

## Goal
- Scaffold implementation aligned to spec/tests.

## Inputs
- API/schema files
- Test stubs (unit/integration/property)

## Outputs
- `src/...` implementation (handlers/services/repos as applicable)
- migrations/seed data if DB is used

## Steps (suggested)
1) Choose stack (web/cli/batch). Default: Fastify + ORM for web API.
2) Implement validation from schema (DTOs)
3) Add repository/service layer with in-memory fallback for tests
4) Add migrations + seeds for integration tests
5) Ensure error handling + pagination per spec

## Commands (example)
- `pnpm run lint`
- `pnpm run test:fast`
