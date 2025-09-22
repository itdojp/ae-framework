# Security/SBOM Label Gates (Issue #964)

Status: Draft (docs-only)

Goals
- Default to report-only on PRs; opt-in execution via labels
- Enforce thresholds only when explicitly requested (label/vars)

Labels and Commands
- Run (PR): `run-security` → executes `sbom-generation.yml` security jobs (and summaries)
- Run (PR): `run-cedar` → executes `cedar-quality-gates.yml` (report-only by default)
- Enforce (PR): `enforce-security` → makes cedar/SBOM checks blocking where supported
- Slash commands:
  - `/run-security`, `/run-security-dispatch` (dispatch on PR head)
  - `/run-cedar`, `/run-cedar-dispatch`
  - `/enforce-security`

Thresholds and Vars
- SBOM/audit gate (PR): defaults from repo vars
  - `SECURITY_MAX_HIGH` (default 0)
  - `SECURITY_MAX_MODERATE` (default 2)
- Cedar quality gates: non-blocking by default; enforcement when `enforce-security` present

Workflow Wiring
- `.github/workflows/sbom-generation.yml`
  - Gated on PR by `run-security`
  - Enforcement step checks `enforce-security` label or `SECURITY_ENFORCE=1`
  - Posts upsert summary with header `<!-- AE-SECURITY-SUMMARY -->` when `run-security`
- `.github/workflows/cedar-quality-gates.yml`
  - Runs when `run-security` or `run-cedar`
  - Fails job when NG>0 AND `enforce-security` is present

Operations
- Start report-only on PRs: add `/run-security` or `/run-cedar`
- Enforce on demand: add `/enforce-security` to turn fails into gates (CI blocking)
- Main branch: prefer scheduled `security.yml` and `sbom-generation.yml` (not label-gated)

Notes
- Comments and summaries should be upserted to avoid noise (fixed headers)
- For dependency tracking, configure `DEPENDENCY_TRACK_URL` and credentials
