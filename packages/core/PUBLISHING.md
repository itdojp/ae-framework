# Publishing @ae-framework/core

`@ae-framework/core` is the standalone minimal assurance runtime for deploy-time
ae-framework profiles. This file records the package publication checklist and
the compatibility boundary used by the composite assurance-gate action.

## Current status

- Package metadata is prepared for `@ae-framework/core@0.1.0`.
- The package is intended for public npm publication under the Apache-2.0
  license, with package-local `LICENSE` and `NOTICE` files included in the
  published artifact.
- Publication is not implied by this repository file. Announce npm availability
  only after `npm publish` succeeds and package provenance is verified.
- The canonical machine-checkable state is
  `docs/operate/publication-evidence.json`. Until its `coreNpmPackage.state` is
  `live`, treat the package as unavailable even if a preflight workflow passed.

## Pre-publish checklist

1. Confirm release owner and npm access for the `@ae-framework` scope.
2. For the initial publish only, create `NPM_BOOTSTRAP_TOKEN` as a protected
   `npm-publish-bootstrap` Environment secret. Use a granular npm access token
   with the minimum package-creation/publish scope, 2FA bypass enabled only when
   required by npm policy, and remove or disable the token immediately after the
   first successful publish.
3. After the package exists, configure npm trusted publishing for this
   repository/package:
   - npm package: `@ae-framework/core`
   - GitHub repository: `itdojp/ae-framework`
   - workflow: `publish-core-package.yml`
   - environment: `npm-publish`
4. Configure the GitHub `npm-publish-bootstrap` and `npm-publish` Environments
   with required reviewers. Do not add a repository-wide npm token.
5. Confirm the publish jobs use GitHub-hosted runners with Node
   `>=22.14.0` and npm CLI `>=11.5.1`.
6. Confirm the action release ref that will consume this package line.
7. From the repository root, run the package checks:

   ```bash
   pnpm --filter @ae-framework/core run build
   pnpm --filter @ae-framework/core run test
   pnpm --filter @ae-framework/core run check:no-src-imports
   (cd packages/core && npm pack --dry-run --json --foreground-scripts=false)
   ```

8. Confirm `npm pack --dry-run` includes `LICENSE` and `NOTICE`.
9. Confirm runtime dependencies remain limited to the documented set:
   `ajv`, `ajv-formats`, and `yaml`.
10. Confirm `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` matches the
   release tag, profile schema, and action metadata.
11. Publish only from the release commit or tag used to document compatibility.

## GitHub Actions workflow

Use `.github/workflows/publish-core-package.yml` for both preflight and publish.
The workflow has three explicit modes:

- `preflight`: no publication; builds, tests, and uploads pack dry-run evidence.
- `bootstrap-token`: initial package creation using the protected
  `npm-publish-bootstrap` Environment and `NPM_BOOTSTRAP_TOKEN`.
- `trusted-publisher`: subsequent publishes using npm trusted publishing and
  the protected `npm-publish` Environment.

### Preflight only (no npm publication)

Run `Publish @ae-framework/core` manually with:

- ref: the release candidate branch or commit
- `package_version`: the version in `packages/core/package.json`
- `publish_mode`: `preflight`

The preflight job installs dependencies, runs the package checks, validates the
requested version, performs `npm pack --dry-run --json`, and uploads
`core-pack-dry-run-<version>` as evidence. The workflow uses
`--foreground-scripts=false` for machine-readable JSON output after the explicit
build and no-source-import checks have already run. This path does not require npm
trusted-publishing configuration and must not be described as a completed
publication.

### Initial publish bootstrap

npm trusted publishing is configured from an existing package's npm settings, so
the first publish cannot rely on OIDC-only trusted publishing. Only a release
owner should run the bootstrap job:

1. Create and push tag `core-v<package_version>` at the reviewed release commit
   (for example, `core-v0.1.0`).
2. Add `NPM_BOOTSTRAP_TOKEN` only to the protected `npm-publish-bootstrap`
   Environment, not as a repository-wide secret.
3. Dispatch `Publish @ae-framework/core` on that exact tag with
   `publish_mode: bootstrap-token`.
4. Approve the `npm-publish-bootstrap` Environment.
5. Confirm the job upgrades npm to `>=11.5.1` and runs on Node `>=22.14.0`.
6. Confirm the job runs `npm publish --provenance --access public` with
   `NODE_AUTH_TOKEN` scoped to the bootstrap Environment.
7. Verify registry state:

   ```bash
   npm view @ae-framework/core version --json
   ```

8. Remove or disable `NPM_BOOTSTRAP_TOKEN`.
9. Configure npm trusted publishing for package `@ae-framework/core`,
   repository `itdojp/ae-framework`, workflow `publish-core-package.yml`, and
   environment `npm-publish`.

### Subsequent trusted-publisher publish

After the initial package exists and npm trusted publishing is configured:

1. Create and push tag `core-v<package_version>` at the reviewed release commit.
2. Dispatch `Publish @ae-framework/core` on that exact tag with
   `publish_mode: trusted-publisher`.
3. Approve the `npm-publish` Environment.
4. Confirm the job upgrades npm to `>=11.5.1` and runs on Node `>=22.14.0`.
5. Confirm the job verifies the package already exists before attempting the
   OIDC trusted-publisher publish.
6. Confirm the job runs `npm publish --provenance --access public` without
   `NODE_AUTH_TOKEN`.
7. Verify registry state:

   ```bash
   npm view @ae-framework/core version --json
   ```

### Post-publish evidence

For either publish mode, run a non-workspace install/import smoke test from a
clean directory:

```bash
npm i @ae-framework/core
node -e "import('@ae-framework/core').then(() => console.log('ok'))"
```

Record the workflow run URL, registry URL, package provenance evidence, and
smoke-test evidence on the release issue before updating QUICKSTART wording.
Then update `docs/operate/publication-evidence.json` in a reviewed PR:

1. set `coreNpmPackage.state` to `live` and clear its blockers;
2. record the exact registry version, successful publish workflow run,
   provenance, non-workspace install/import evidence, verification timestamp,
   public verifier identifier, and `release-owner` verifier role; use only the
   repository/npm/Sigstore public URL forms allowed by the schema;
3. run `pnpm -s run publication:evidence:validate` without network access;
4. do not commit tokens, private evidence locations, or a generated candidate
   as owner verification.

## Compatibility rule

The composite action builds `@ae-framework/core` from the downloaded action
repository ref for the one-workflow-file path. Keep the action ref, profiles,
policy, schema bundle, and package release line aligned. Historical pre-`v1`
previews used `main` or explicit commit SHA pins; now that the `v1` action tag is
live, external quickstart users can use `itdojp/ae-framework@v1` for the action.
The npm package remains unpublished until the release-owner workflow publish
succeeds and `npm view @ae-framework/core version` verifies registry state.
