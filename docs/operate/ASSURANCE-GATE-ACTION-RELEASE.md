---
docRole: ssot
lastVerified: '2026-07-12'
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

## External runtime smoke sequence

Path resolution proves only that `action.yml` exists at a ref. It does not prove
that the composite action can complete setup, frozen install, build, policy
evaluation, or output generation on a hosted runner. Before a release owner
makes a Marketplace availability claim, use a public consumer repository other
than `itdojp/ae-framework` and preserve public Actions evidence in this order:

1. Run pass and block (`fail-on-block=false`) fixtures against the reviewed
   candidate commit SHA. Do not create the immutable tag after a failed
   candidate run.
2. Create the immutable `v1.x.y` tag and GitHub Release on that exact candidate,
   then run the same pass and block fixtures against the immutable ref.
3. Confirm the immutable ref resolves to the candidate commit. Only then move
   `v1` to the same commit and repeat both fixtures against `@v1`.
4. Record the immutable and moving-ref run URLs, resolved commits, verification
   timestamps, verifier identity, gate results, and the presence of
   `gate-result.json`, `assurance-summary.json`, `policy-decision.json`, and
   `review-surface.md` in `docs/operate/publication-evidence.json`. Record each
   pass/block job name so `(workflowRunUrl, jobName)` uniquely locates all four
   immutable/moving cases, including a single matrix workflow run.

The checked-in contract currently allowlists the public consumer repository
`itdojp/ae-framework-impl-test-hub`. Both refs must resolve to the same lowercase
40-character commit SHA. The block fixture must complete its job successfully
with `fail-on-block=false`, preserve a `gateResult` of `block`, and record the
missing-evidence decision rather than converting it to a pass.

The default validator is deterministic and offline: it validates checked-in
shape, public URL allowlists, expected pass/block semantics, required artifact
names, action-ref/tag consistency, and resolved-commit parity. It does not replay
the workflow or authorize tag mutation. Tag creation, moving `v1`, GitHub Release
creation, Marketplace publication, and the reviewed evidence PR remain
release-owner operations. Runtime smoke is report-only release evidence; it is
not an approval, safety, productivity, or adoption claim and is not a normal-PR
wall-clock gate.

## Marketplace publication boundary

The repository can prepare Marketplace-compatible metadata in code, but the
listing is not considered live until the release owner publishes it in GitHub
Marketplace, records the listing URL in the release note and #3626, and records
the external immutable/moving-tag runtime smoke described above. Do not claim
Marketplace availability from the presence of `action.yml`, tags, or successful
path resolution alone.
The canonical state is `assuranceGateMarketplace` in
`docs/operate/publication-evidence.json`. After owner-operated publication,
update that surface in a reviewed PR with the live listing URL, release note,
external action-path resolution evidence, both runtime smoke refs, verification
timestamp, and public verifier identifier with the `release-owner` role. Use
only the repository and Marketplace public URL forms allowed by the schema.
Clear blockers only when those public evidence fields are present, then run
`pnpm -s run publication:evidence:validate`.

## Startup/runtime measurement boundary

The current composite action intentionally prepares Corepack/pnpm, installs the
core dependency graph, and builds `@ae-framework/core` from the selected action
ref before running the gate. Cold and warm overhead for those phases is measured
by the report-only harness in
`docs/operate/ASSURANCE-GATE-STARTUP-BENCHMARK.md`. The benchmark is not a
productivity or review-speed claim and is not a normal-PR required check.

Use its exact-ref JSON/Markdown report when diagnosing registry latency, cache
behavior, or build-dominated startup. Do not switch the action to an unpublished
npm package or prebuilt/bundled surface without a separate compatibility and
rollback decision.

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
