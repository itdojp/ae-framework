# Live Operational Posture Audit Checklist

`ae-framework` のソース監査は、GitHub repository settings、branch/ruleset protection、Actions approval policy、repo secrets/variables、runner network posture などのライブ運用設定を直接証明できません。この文書は、source finding と live control evidence を分離し、未取得のライブ証跡を residual risk として明示するための checklist と collector の運用手順を定義します。

## Scope / 対象

この checklist は以下を対象にします。

- branch protection / repository rulesets
- GitHub Actions workflow permissions and fork PR approval policy
- Actions secrets / variables inventory without exposing values
- hosted/self-hosted runner inventory and runner trust boundary
- runner egress / network control evidence supplied by an operator
- reconciliation between local source findings and live operational controls

この checklist は source-level CI validation の代替ではありません。Live evidence が未取得の場合、collector は成功終了しても report 内で `missing-evidence` として明示します。

## Collector

Deterministic no-live report:

```bash
node scripts/security/collect-live-posture.mjs \
  --repo itdojp/ae-framework \
  --no-live
```

Live GitHub collection with `gh`:

```bash
node scripts/security/collect-live-posture.mjs \
  --repo itdojp/ae-framework \
  --output-json artifacts/security/live-operational-posture.json \
  --output-md artifacts/security/live-operational-posture.md
```

Fixture-based report for review or tests:

```bash
node scripts/security/collect-live-posture.mjs \
  --fixture artifacts/security/live-posture-fixture.json \
  --output-json artifacts/security/live-operational-posture.json \
  --output-md artifacts/security/live-operational-posture.md
```

The collector uses GitHub REST endpoints through `gh api` when live mode is enabled. If an endpoint is unavailable, unauthorized, or not expressible through GitHub API (for example runner egress controls), the report keeps the evidence entry as `missing` and the associated checklist row as `missing-evidence`.

## Checklist

| Area | Required evidence | Live source | Operator decision |
| --- | --- | --- | --- |
| Branch/ruleset protection | Default branch protection or repository rulesets exist; required PR review and required status checks are reviewed. | `repos/{owner}/{repo}/branches/{branch}/protection`, `repos/{owner}/{repo}/rulesets` | Confirm required checks match branch protection and bypass actors are intentional. |
| Workflow permissions | Default `GITHUB_TOKEN` permission and Actions PR review approval capability are known. | `repos/{owner}/{repo}/actions/permissions/workflow` | Prefer read-only default token; document each workflow that requires write permissions. |
| Actions approval policy | Fork PR workflow approval policy and allowed Actions policy are known. | `repos/{owner}/{repo}/actions/permissions`, fork PR approval endpoint when available | Confirm fork PR approval behavior before relying on PR-originated artifacts. |
| Secrets / variables | Secrets and variables inventory is collected by count/source without values. | `repos/{owner}/{repo}/actions/secrets`, `repos/{owner}/{repo}/actions/variables` | Review naming, owner, rotation, and whether any write-token secret can reach PR-exposed workflows. |
| Runner inventory | Hosted/self-hosted runner inventory and labels are reviewed. | `repos/{owner}/{repo}/actions/runners` | If self-hosted runners exist, document trust boundary, cleanup, labels, and PR exposure policy. |
| Runner egress | Network egress restrictions, proxy/DNS controls, and dependency-fetch exceptions are attached as operator evidence. | Operator-supplied evidence; GitHub source/API alone is insufficient. | Keep this item as residual risk until an operator attaches evidence. |
| Source finding linkage | Live evidence status is linked back to source findings and residual risks. | Collector report summary | Do not close source-audit residual risk solely because source code changed. |

## Report interpretation

The JSON report uses `schemaVersion: live-operational-posture/v1` and records:

- `evidenceMode`: `live`, `fixture`, or `not-collected`
- `evidence`: per-source status (`collected` or `missing`)
- `checklist`: operator-facing controls with `satisfied`, `needs-review`, or `missing-evidence`
- `summary.missingEvidenceIds`: live evidence gaps that must remain visible in release or security review notes

A `satisfied` checklist row means the collector found enough live evidence to support review. It does not mean the control is approved by policy. Human/operator review is still required for bypass actors, runner labels, private workflows, and network boundaries.

## Residual risk policy

- If `summary.missingEvidenceIds` is non-empty, the corresponding source finding remains a residual operational risk.
- If live evidence cannot be collected due permissions, record the missing endpoint and request repository administrator evidence instead of substituting source-code inference.
- If self-hosted runners or write-token workflows are present, the report should be attached to the PR/Issue that changes automation trust decisions.
