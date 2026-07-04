# Publishing @ae-framework/core

`@ae-framework/core` is the standalone minimal assurance runtime for deploy-time
ae-framework profiles. This file records the package publication checklist and
the compatibility boundary used by the composite assurance-gate action.

## Current status

- Package metadata is prepared for `@ae-framework/core@0.1.0`.
- The package is intended for public npm publication under the Apache-2.0
  license.
- Publication is not implied by this repository file. Announce npm availability
  only after `npm publish` succeeds and package provenance is verified.

## Pre-publish checklist

1. Confirm release owner and npm access for the `@ae-framework` scope.
2. Confirm the action release ref that will consume this package line.
3. From the repository root, run the package checks:

   ```bash
   pnpm --filter @ae-framework/core run build
   pnpm --filter @ae-framework/core run test
   pnpm --filter @ae-framework/core run check:no-src-imports
   (cd packages/core && npm pack --dry-run)
   ```

4. Confirm runtime dependencies remain limited to the documented set:
   `ajv`, `ajv-formats`, and `yaml`.
5. Confirm `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` matches the
   release tag, profile schema, and action metadata.
6. Publish only from the release commit or tag used to document compatibility.

## Compatibility rule

The composite action builds `@ae-framework/core` from the downloaded action
repository ref for the one-workflow-file path. Keep the action ref, profiles,
policy, schema bundle, and package release line aligned. Before a `v1` action
tag exists, external quickstart users should pin the action to `main` or to an
explicit commit SHA for preview validation.
