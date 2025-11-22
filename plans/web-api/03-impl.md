# ExecPlan: Web API / 03-impl

## Goal
- Scaffold minimal implementation aligned to spec/tests with DB migrations.

## Inputs
- `spec/api/openapi.yml`
- Test stubs from `tests/integration/web-api/`

## Outputs
- `src/web-api/` handlers/controllers/services
- `src/web-api/db/migrations/*.sql|ts`
- `src/web-api/db/schema.ts` (ORM schema if applicable)
- Wiring for dependency injection/config

## Steps
1) Decide stack (Fastify/Express/Nest). Default: Fastify + Prisma/Drizzle placeholder.
2) Implement DTO/validation from OpenAPI schemas.
3) Add repository/service layer with in-memory fallback for tests.
4) Add migrations + seed data for integration tests.
5) Ensure handlers return spec-compliant errors and pagination.

## Commands (suggested)
- `pnpm run lint`
- `pnpm run test:fast`
- Optional: `pnpm run pipelines:mutation:quick` (time-boxed)
