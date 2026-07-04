# @ae-framework/core

Standalone minimal assurance runtime for deploy-time ae-framework profiles.

This package is intentionally independent of the repository root `src/**` tree. It provides:

- curated artifact/schema validation with AJV;
- deploy-time assurance profile parsing and validation;
- minimal lane/evidence aggregation into `assurance-summary/v1` shape;
- pure-JS YAML release-policy evidence checks;
- PR review surface Markdown rendering.

## Runtime dependency rationale

Runtime dependencies are intentionally limited to three packages:

| Dependency | Rationale |
| --- | --- |
| `ajv` | Validates the curated JSON Schema 2020-12 contracts shipped with the package. |
| `ajv-formats` | Enforces format assertions such as `date-time`, matching repository validators. |
| `yaml` | Parses deploy-time profiles and release policies without requiring repository tooling. |

The package has no workspace or repository-root runtime dependency and must not import from `src/**`.
The shipped `schema/` files are copied from the repository root contracts and guarded by API tests so standalone installs can validate artifacts without a monorepo checkout.

## Development checks

```bash
pnpm --filter @ae-framework/core run build
pnpm --filter @ae-framework/core run test
pnpm --filter @ae-framework/core run check:no-src-imports
```
