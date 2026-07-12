---
docRole: derived
canonicalSource:
- action.yml
- .github/actions/assurance-gate/action.yml
- .github/actions/assurance-gate/README.md
- packages/core/README.md
- docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md
- docs/operate/publication-evidence.json
- tests/actions/assurance-gate-action.test.ts
- tests/cli/init-cli.test.ts
lastVerified: '2026-07-12'
owner: product-assurance
verificationCommand: pnpm -s exec vitest run tests/actions/assurance-gate-action.test.ts tests/unit/docs/publish-assets-quickstart.test.ts --reporter dot
---

# 15-minute quickstart: one workflow file assurance gate

This quickstart is for a fresh external GitHub repository that does not use the
ae-framework pnpm workspace. It uses one workflow file to exercise the
`minimal` deploy-time profile, produce assurance gate artifacts, and render a
review surface in the workflow summary.

Publication boundary: use the root action ref `itdojp/ae-framework@v1` for the
normal adoption path after the `v1` tag exists. Pin an exact tag or commit SHA
for reproducible evaluation. Do not describe the npm package or Marketplace
listing as live unless the release note for that publication exists.
The machine-checkable current state is
`docs/operate/publication-evidence.json`; a prepared workflow, action tag, or
metadata file does not by itself change a surface to `live`.
Likewise, resolving `action.yml` at a tag proves only path availability. The
Marketplace surface requires public external-consumer pass and block runtime
evidence for both the immutable release tag and moving `@v1` before it can be
recorded as `live`; see `docs/operate/ASSURANCE-GATE-ACTION-RELEASE.md`.

## What this proves

| Result | Evidence in this repository |
| --- | --- |
| A bare non-workspace fixture can pass the minimal assurance gate. | `tests/actions/assurance-gate-action.test.ts` creates a temporary external-style workspace and receives `Policy decision: pass`. |
| The same fixture can produce a blocking gate decision for missing required evidence. | The action test records `policyResult: block` and a review surface when `qualityGates` evidence is omitted. |
| The CLI scaffold uses the same action surface. | `tests/cli/init-cli.test.ts` verifies the generated workflow uses `.github/actions/assurance-gate`. |
| The action, profile, schema, and core compatibility boundary is documented. | `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md`. |

The quickstart does not claim production adoption, Marketplace publication,
npm availability, review speed, safety improvement, or agent/vendor superiority.

## Prerequisites

- A GitHub repository where you can add one workflow file.
- GitHub Actions enabled.
- The workflow grants `contents: read` and `actions: read`; the latter keeps artifact upload compatible with repositories that restrict default token permissions.
- No ae-framework checkout, pnpm workspace, GitHub token, hosted LLM API, or
  external agent service is required in the consumer repository.
- The action runtime uses Node/Corepack inside the downloaded ae-framework action
  repository; consumer repositories only supply evidence artifacts.
- The action currently performs Corepack/pnpm setup, a filtered core dependency
  install, and a core build before gate execution. See
  `docs/operate/ASSURANCE-GATE-STARTUP-BENCHMARK.md` for the report-only cold/warm
  measurement method. Registry/cache delay is startup friction, not a gate
  decision or approval signal.

## Step 1: Add one workflow file

Create `.github/workflows/ae-assurance.yml` in the consumer repository:

```yaml
name: ae assurance quickstart

on:
  pull_request:
  workflow_dispatch:
    inputs:
      mode:
        description: Produce a passing or blocking assurance decision.
        type: choice
        required: true
        default: pass
        options:
          - pass
          - block
      enforce:
        description: Fail the job when the policy result is block.
        type: boolean
        required: true
        default: false

permissions:
  contents: read
  actions: read

jobs:
  assurance:
    runs-on: ubuntu-latest
    steps:
      - name: Prepare minimal assurance evidence
        shell: bash
        env:
          MODE: ${{ github.event.inputs.mode || 'pass' }}
        run: |
          set -euo pipefail
          mkdir -p artifacts
          if [ "$MODE" = "block" ]; then
            cat > artifacts/evidence.json <<'JSON'
          {
            "evidence": [
              {
                "claimId": "minimal-assurance-gate-reviewable",
                "lane": "spec",
                "kind": "schema",
                "sourceKind": "spec-derived",
                "origin": "quickstart-fixture"
              }
            ],
            "policyEvidence": ["postDeployVerify"]
          }
          JSON
          else
            cat > artifacts/evidence.json <<'JSON'
          {
            "evidence": [
              {
                "claimId": "minimal-assurance-gate-reviewable",
                "lane": "spec",
                "kind": "schema",
                "sourceKind": "spec-derived",
                "origin": "quickstart-fixture"
              },
              {
                "claimId": "minimal-assurance-gate-reviewable",
                "lane": "behavior",
                "kind": "integration",
                "sourceKind": "runtime-derived",
                "origin": "quickstart-fixture"
              }
            ],
            "policyEvidence": ["postDeployVerify", "qualityGates"]
          }
          JSON
          fi

      - name: Run ae-framework assurance gate
        id: assurance
        uses: itdojp/ae-framework@v1
        with:
          profile: minimal
          artifacts-dir: artifacts
          output-dir: artifacts/assurance-gate
          fail-on-block: ${{ github.event.inputs.enforce || 'false' }}

      - name: Add review surface to job summary
        if: always()
        shell: bash
        run: |
          set -euo pipefail
          review_surface="artifacts/assurance-gate/review-surface.md"
          gate_result="artifacts/assurance-gate/gate-result.json"
          if [ -f "$review_surface" ]; then
            cat "$review_surface" >> "$GITHUB_STEP_SUMMARY"
          fi
          if [ -f "$gate_result" ]; then
            printf '\n## Gate result\n\n```json\n' >> "$GITHUB_STEP_SUMMARY"
            cat "$gate_result" >> "$GITHUB_STEP_SUMMARY"
            printf '\n```\n' >> "$GITHUB_STEP_SUMMARY"
          fi

      - name: Upload assurance artifacts
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: ae-assurance-gate
          path: artifacts/assurance-gate
```

For a reproducible evaluation, replace `@v1` with `@v1.0.2` after that release
exists, or use a specific commit SHA from `itdojp/ae-framework`. During release
preparation, pin the reviewed candidate SHA until the immutable tag is created.

## Step 2: Run pass mode

Open the Actions tab and run `ae assurance quickstart` with:

- `mode`: `pass`
- `enforce`: `false`

Expected result:

- the workflow job succeeds;
- `artifacts/assurance-gate/gate-result.json` contains `"policyResult": "pass"`;
- the job summary includes a review surface headed by `Policy decision: pass`;
- the uploaded artifact contains `assurance-summary.json`, `policy-decision.json`,
  `review-surface.md`, and `gate-result.json`.

This is the fastest path for confirming that the consumer repository can run the
minimal gate without adopting the ae-framework workspace.

## Step 3: Run block mode

Run the same workflow with:

- `mode`: `block`
- `enforce`: `false`

Expected result:

- the workflow job succeeds so the review surface and artifacts are retained;
- `gate-result.json` contains `"policyResult": "block"`;
- `policy-decision.json` lists missing evidence, including `qualityGates`;
- the job summary shows `Policy decision: block`.

Then run again with `mode: block` and `enforce: true` to see the workflow fail as
a blocking gate. Use `enforce: false` while learning the artifact shape, and use
`enforce: true` only when the repository is ready for the gate to control PR
status.

## Step 4: Move from fixture evidence to repository evidence

The workflow above writes fixture evidence inline so the setup remains one file.
A real repository should eventually replace the `Prepare minimal assurance
evidence` step with producer steps that write `artifacts/evidence.json` or
schema-validated artifacts. Keep these rules:

1. Keep `profile: minimal` until the repository can consistently produce the
   required minimal evidence.
2. Change only the `profile` input to evaluate `standard` or `full` after the
   additional evidence producers exist.
3. Pin the action ref to the release line or commit used for compatibility
   evaluation.
4. Treat the review surface as decision support. It is not approval, merge
   authority, or a live pilot outcome claim.

## Compatibility and publication notes

- `@ae-framework/core` is prepared with npm metadata for `0.1.0`, but this
  quickstart does not require consumers to install it directly.
- The root composite action builds the core package from the same action
  repository ref, which keeps action/profile/schema/core versions aligned.
- Marketplace-compatible root action metadata is present in `action.yml`, but
  Marketplace publication is separate from this checked-in path and still
  requires the release owner to publish the listing and record immutable and
  moving-tag external runtime smoke. A successful path-resolution check is not
  runtime evidence.
- See `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` for the version-skew
  boundary and the `@v1` / exact-tag / commit-SHA transition.

## Troubleshooting

| Symptom | Likely cause | Disposition |
| --- | --- | --- |
| `policyResult` is `block` in pass mode | The inline evidence step was edited or `qualityGates` / behavior evidence is missing. | Compare the workflow with the pass-mode JSON above. |
| The job fails in block mode | `enforce` is `true`, so a block decision is intentionally enforced. | Re-run with `enforce: false` to inspect artifacts without failing the job. |
| The action ref cannot be resolved | `@v1.0.2` was used before the immutable tag was created, or a commit SHA was typed incorrectly. | Use `@v1.0.2` only after the release exists, or pin the reviewed ae-framework release commit SHA. |
| The review surface is missing from the summary | The action failed before writing outputs. | Download logs and check the build/corepack step first, then inspect uploaded artifacts if present. |
