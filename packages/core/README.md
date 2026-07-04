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

## Publication metadata

The package metadata is prepared for public npm publication as
`@ae-framework/core@0.1.0` under Apache-2.0. The package is not considered
published until the release owner executes and verifies the npm publish step.

Publication-facing metadata is recorded in `package.json`:

- `license`: Apache-2.0
- `publishConfig.access`: public
- repository directory: `packages/core`
- runtime files: `dist`, `schema`, `README.md`, and `PUBLISHING.md`
- Node engine: `>=20.11 <23`

Use `PUBLISHING.md` for the pre-publish checklist.

## Compatibility with the action and profiles

The composite assurance-gate action builds this package from the same repository
ref that supplies the action metadata, built-in profiles, release policy, and
curated schema bundle. Keep those surfaces aligned by pinning the action to a
release tag or commit SHA when evaluating external repositories.

See `../../docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` for the
version-skew boundary and the transition from preview refs (`main` or a commit
SHA) to the planned `v1` action ref.
