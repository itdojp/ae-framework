---
docRole: ssot
lastVerified: '2026-07-06'
owner: product-assurance
verificationCommand: pnpm -s exec vitest run tests/actions/assurance-gate-action.test.ts tests/cli/init-cli.test.ts tests/unit/docs/publish-assets-quickstart.test.ts --reporter dot
---

# Assurance Gate action release policy

This runbook defines the release policy for the root `ae-framework Assurance
Gate` action used by external repositories.

## Action surfaces

| Surface | Purpose | Status |
| --- | --- | --- |
| `action.yml` at repository root | Marketplace-compatible action metadata and the stable external action surface: `itdojp/ae-framework@v1`. | Release surface. |
| `.github/actions/assurance-gate/action.yml` | Backward-compatible subdirectory action used by existing preview documentation and tests. | Compatibility surface. |

GitHub Marketplace requires the action metadata file (`action.yml` or
`action.yaml`) at the repository root for automatic listing. The root action is
therefore the action that should receive the next immutable `v1.x.y` release tag and the moving `v1` tag.

## Tag policy

Use two tags for the action release line:

| Tag | Mutability | Purpose |
| --- | --- | --- |
| `v1.0.1` | Immutable after publication. | Exact release tag for the first root action publication in this repository; `v1.0.0` already exists as a historical bootstrap tag and must not be rewritten. |
| `v1` | Moving major tag. | Consumer-friendly stable major line for quickstarts and `ae init`. |

After the PR that changes the action release surface is merged to `main`, create
or update the tags from the verified merge commit:

```bash
git fetch origin main --tags
git checkout main
git pull --ff-only origin main
MERGE_SHA=$(git rev-parse HEAD)
git tag -a v1.0.1 "$MERGE_SHA" -m "Release ae-framework Assurance Gate v1.0.1"
git tag -f -a v1 "$MERGE_SHA" -m "Move ae-framework Assurance Gate v1 to v1.0.1"
git push origin v1.0.1
git push origin v1 --force
```

Only move `v1` to a later `v1.x.y` release after:

1. root `action.yml` and `.github/actions/assurance-gate/action.yml` remain
   semantically compatible;
2. `tests/actions/assurance-gate-action.test.ts` passes for root and subdirectory
   `GITHUB_ACTION_PATH` detection;
3. `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` is updated if profile,
   schema, policy, or core compatibility changes;
4. PR required checks and full rollup are green.

## Marketplace publication boundary

The repository can prepare Marketplace-compatible metadata in code, but the
listing is not considered live until the release owner publishes it in GitHub
Marketplace and records the listing URL in the release note and #3626. Do not
claim Marketplace availability from the presence of `action.yml` or tags alone.

## Consumer guidance

Use the moving major tag for normal adoption:

```yaml
uses: itdojp/ae-framework@v1
```

Use a full tag or commit SHA when reproducibility matters:

```yaml
uses: itdojp/ae-framework@v1.0.1
# or: uses: itdojp/ae-framework@<commit-sha>
```
