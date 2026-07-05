---
docRole: derived
canonicalSource:
- docs/getting-started/QUICKSTART-15MIN.md
- docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md
- packages/core/package.json
- packages/core/README.md
- .github/actions/assurance-gate/action.yml
- .github/actions/assurance-gate/README.md
- docs/quality/DEPLOY-TIME-PROFILE-DOGFOOD.md
lastVerified: '2026-07-04'
owner: product-assurance
verificationCommand: pnpm -s exec vitest run tests/unit/docs/publish-assets-quickstart.test.ts --reporter dot
---

# Deploy-time profile publish assets 2026-07-04

This file prepares outward-facing assets for Issue #3620. It is intentionally
claim-limited: it distinguishes checked-in implementation from future npm and
Marketplace publication steps.

## Publication status

| Surface | Status as of 2026-07-04 | Public wording boundary |
| --- | --- | --- |
| `@ae-framework/core` package metadata | Prepared in `packages/core/package.json` with Apache-2.0 license, repository metadata, keywords, public publish config, Node engine, and three runtime dependencies. | Say the package metadata is ready for publication review. Do not say the package is available on npm until the npm publish step is executed and verified. |
| Composite action metadata | Marketplace-compatible root `action.yml` and subdirectory compatibility metadata are prepared with name, description, inputs, outputs, and branding. | Say the action release surface is prepared for `itdojp/ae-framework@v1`. Do not say Marketplace publication is complete until the listing is published and its URL is recorded. |
| 15-minute external quickstart | Prepared in `docs/getting-started/QUICKSTART-15MIN.md`. | Say a one-workflow-file preview path is documented and covered by repository tests. Do not claim external live adoption or production outcomes. |
| Compatibility reference | Prepared in `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md`. | Say action/profile/schema/core version-skew boundaries are documented. |
| Dogfood evidence | Prepared in `docs/quality/DEPLOY-TIME-PROFILE-DOGFOOD.md` and fixture replay tests. | Say the repository dogfoods profile replay against fixtures. Do not claim all external repositories will match this repo's full profile decisions. |

## npm package listing draft

| Field | Draft value |
| --- | --- |
| Package | `@ae-framework/core` |
| Version line | `0.1.x` initial preview line |
| Description | Standalone minimal assurance core for ae-framework deploy-time profiles. |
| License | Apache-2.0 |
| Runtime dependencies | `ajv`, `ajv-formats`, `yaml` |
| Node engine | `>=20.11 <23` |
| Keywords | `assurance`, `policy-gate`, `github-actions`, `software-supply-chain`, `agentic-sdlc`, `ai-code-review`, `formal-methods`, `json-schema` |
| Repository directory | `packages/core` |

Suggested npm README lead:

```markdown
@ae-framework/core is the standalone minimal assurance runtime for ae-framework
deploy-time profiles. It validates curated assurance artifacts, aggregates a
minimal assurance summary, evaluates a pure-JS YAML release policy, and renders
review-surface Markdown without importing from the repository `src/**` tree.
```

Do not publish the package until the release owner confirms package access,
provenance settings, and the release tag/commit used for action compatibility.

## GitHub Marketplace listing draft

| Field | Draft value |
| --- | --- |
| Name | ae-framework Assurance Gate |
| Short description | Validate assurance artifacts, evaluate a deploy-time profile policy, and render a PR review surface. |
| Icon / color | `shield` / `blue` |
| Primary category | Code quality |
| Secondary category | Security |
| Inputs | `profile`, `artifacts-dir`, `policy`, `output-dir`, `environment`, `fail-on-block` |
| Outputs | `gate-result`, `gate-result-path`, `assurance-summary-path`, `policy-decision-path`, `review-surface-path` |
| First-run doc | `docs/getting-started/QUICKSTART-15MIN.md` |
| Compatibility doc | `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` |

Suggested Marketplace overview:

```markdown
ae-framework Assurance Gate runs a deploy-time assurance profile in a consumer
GitHub repository. The minimal profile validates submitted assurance artifacts,
aggregates a reviewable summary, evaluates a declarative policy gate, and writes
review-surface artifacts that can be attached to a PR workflow summary.
```

Suggested boundary paragraph:

```markdown
The action is an assurance gate and review-surface renderer. It is not an agent
runtime, auto-merge authority, hosted CI service, or evidence that a repository
has improved review speed, safety, or adoption outcomes.
```

## Repository description and topic guidance

| Surface | Guidance |
| --- | --- |
| Repository description | `Agent-neutral assurance control plane for agent-driven SDLC.` |
| Topics | `agentic-sdlc`, `assurance`, `policy-gates`, `ai-code-review`, `github-actions`, `software-supply-chain`, `formal-methods`, `json-schema`, `devex` |
| Tagline | `Bring your own agent. Keep your assurance plane.` |

Use these as repository metadata candidates only. Changing GitHub repository
settings is operationally separate from this documentation PR.

## Release note draft

### Title
Deploy-time profiles: standalone core package assets and one-workflow-file assurance gate quickstart

### Summary
This release prepares the external adoption surface for ae-framework deploy-time
profiles. The repository now includes npm-ready metadata for `@ae-framework/core`,
Marketplace listing draft metadata for the composite assurance-gate action, a
compatibility reference for action/profile/schema/core version alignment, and a
15-minute external repository quickstart that uses one workflow file to produce
pass and block gate decisions with review-surface artifacts.

### What's implemented

- `@ae-framework/core` package metadata and documentation for the standalone
  minimal assurance runtime.
- Composite action metadata, branding, input/output documentation, and first-run
  links for `.github/actions/assurance-gate/`.
- `docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md` for version-skew rules.
- `docs/getting-started/QUICKSTART-15MIN.md` for the one-workflow-file preview
  path.
- Tests covering metadata, documentation links, pass/block quickstart behavior,
  and publication-status boundaries.

### What's not yet claimed

- npm publication is not claimed until `@ae-framework/core` is actually published
  and verified.
- Marketplace publication is not claimed until the action listing is published and the listing URL is recorded.
- External live adoption, production effectiveness, review-speed improvement,
  safety improvement, and agent/vendor superiority are not claimed by these
  assets.

## Announcement copy

### Short post

```text
ae-framework now has the publish/adoption assets for deploy-time profiles:

- npm-ready metadata for @ae-framework/core
- Marketplace listing draft metadata for the assurance-gate composite action
- action/profile/schema/core compatibility reference
- a 15-minute external-repo quickstart using one workflow file

Boundary: this prepares the publication surface. It does not claim npm or
Marketplace publication until those release steps are executed, and it does not
claim live external adoption or review-speed/safety outcomes.

Start: docs/getting-started/QUICKSTART-15MIN.md
Compatibility: docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md
```

### Longer post

```text
We prepared the external adoption surface for ae-framework deploy-time profiles.

The new 15-minute quickstart is intentionally small: add one GitHub workflow file
to a fresh repository, run the minimal assurance gate, and inspect pass/block
policy decisions plus the generated review surface. The consumer repository does
not need the ae-framework pnpm workspace.

The checked-in assets now cover:

- @ae-framework/core package metadata for the standalone minimal assurance runtime;
- Marketplace-compatible metadata for the root assurance-gate action;
- a compatibility reference explaining how action refs, profiles, schemas, and
  core versions must stay aligned;
- release copy that separates implemented behavior from planned npm and
  Marketplace publication.

Claim boundary: this is publication readiness, not proof of external production
adoption. npm and Marketplace availability should only be announced after those
release steps are executed and verified. Review speed, safety, adoption impact,
and agent-vendor comparisons remain unsupported by this evidence.

Start: docs/getting-started/QUICKSTART-15MIN.md
Compatibility: docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md
```

## Supported / unsupported claim checklist

| Claim | Status | Evidence or disposition |
| --- | --- | --- |
| The repository contains npm-ready metadata for `@ae-framework/core`. | Supported | `packages/core/package.json` and `packages/core/README.md`. |
| The repository contains Marketplace-compatible action metadata. | Supported | Root `action.yml`, `.github/actions/assurance-gate/action.yml`, and action README; Marketplace publication still needs listing evidence. |
| A one-workflow-file preview quickstart exists for external repositories. | Supported | `docs/getting-started/QUICKSTART-15MIN.md`. |
| Pass and block gate decisions are covered by repository tests. | Supported | `tests/actions/assurance-gate-action.test.ts`. |
| The package is published on npm. | Unsupported until release execution | Requires npm publish evidence. |
| The action is published in GitHub Marketplace. | Unsupported until release execution | Requires Marketplace listing evidence. |
| External repositories have adopted the gate in production. | Unsupported | No live external adoption evidence is recorded here. |
| ae-framework improves review speed, safety, or quality in general. | Unsupported | No controlled comparison result is recorded here. |
