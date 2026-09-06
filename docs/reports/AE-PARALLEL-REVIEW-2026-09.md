---
docRole: derived
canonicalSource:
- docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
- docs/integrations/CODEX-ISSUE-RUNBOOK.md
- scripts/agents/github-work-state-lib.mjs
- scripts/codex/adapter-stdio.mjs
lastVerified: '2026-09-07'
---

# Parallel Assurance Review — September 2026

## Status and scope

Review date: 2026-09-07 JST. Tracking deliverable: [#3675][review].
Inspected main: `c5da6115638fdbfeebbc458b39fa6916db66afb0`.

This is a dated source-level review and implementation proposal. It is not a
live status page, merge approval, security certification, or replacement for
canonical policy. Follow-up implementations are not completed by this report.

日本語要約: 製品方針の全面変更ではなく、観測・実行結果・受入判定・人間判断の
境界を明確化する。実行中のコンテナ修復には変更を加えず、重複する改善は既存の
Issueへ補足し、新規課題は別Issueとして扱う。このレビューを既存PRの追加の
完了条件にしない。

The active recovery surfaces are Issue #3672 / PR #3674 and Issue #3671 /
PR #3673. This review does not write their branches, change readiness, retarget
bases, alter labels or comments, resolve threads, or dispatch their workflows.
The documentation uses a separate branch and a new path.

## Product assessment

The [product policy][product] describes an agent-neutral judgment layer rather
than a replacement coding agent. It already distinguishes claim status,
execution evidence, assurance projection and human override, and requires
risk-based verification. The direction remains appropriate for the observed
problems; another agent harness or a wholesale repository rewrite is not the
recommended response.

The main opportunity is to turn repeated operator decisions into small,
explicit contracts without creating a new mandatory gate for every change.
The proposed boundaries are:

| Layer | Question | Not equivalent to |
| --- | --- | --- |
| Observation | What did the API or tool report? | Successful execution |
| Execution | What actually ran and happened? | Claim satisfaction |
| Integrity | Does the record match its schema and digest? | Trusted origin |
| Acceptance | Does evidence satisfy this scoped plan? | Merge permission |
| Human decision | What exact material did an authorized human decide on? | Independent review when none occurred |
| Publication | Was this artifact explicitly approved for this destination? | A successful private export |

An observation can be stable but blocked. A digest can be correct but belong to
the wrong task. A scan can execute successfully and still report vulnerabilities.
A focused runtime test does not establish whole-product security.

## Source findings and ownership

### Authority consumers need independent subject binding

The [snapshot resolver][authority] verifies a local regular non-symlink file,
Schema, semantic consistency and an expected digest. Its options do not bind
expected repository, Issue, PR or source head. The [stdio consumer][stdio]
supplies only the local root and digest to that resolver.

This is a source-level gap between integrity validation and task validation,
not evidence of a demonstrated remote exploit. A copied valid snapshot must not
become the current task's authority merely because its digest recomputes.

[#3676][binding] tracks trusted expected-subject inputs, explicitly
non-authoritative informational imports, bounded strict parsing and a separate
freshness decision. The expected identity must come from the operator/control
plane, not from the same snapshot or model output being checked. Offline
validation remains separate from optional trusted live revalidation.

### Check identity must not imply a different API resource

`normalizeCheckNode()` stores `CheckRun.databaseId` under `runId`. The
[capture query][capture] does not obtain an Actions workflow-run identity.
Consequently, the field must not be passed to `gh run view` as though it were a
workflow-run ID.

[#3676][binding] also tracks typed check-run, check-suite, workflow-run and
attempt identities with nullable unobserved metadata and an explicit migration.
It must distinguish PR source head, test-merge SHA and main merge SHA. External
check providers must not acquire fabricated GitHub Actions run identifiers.

### Stable snapshots are not acceptance decisions

The [runbook][runbook] correctly says that timestamp-only changes are not
progress. Its `no-state-change` comparison says nothing about whether the stable
state meets the current acceptance conditions.

[#3677][acceptance] proposes a report-only acceptance-plan/evaluator boundary.
A plan fixes subject, phase, workflow/job identity, event, mode, enforcement,
SHA relationship, evidence coverage, freshness and retry budget. A report keeps
`pending`, `blocked` and `observation-error` distinct from readiness for human
review. These are decision states, not replacements for #3658 execution states.

An API error must not be parsed as an ID. An incomplete page or an empty list
must not satisfy an all-success check. A failed workflow remains failed even
when every materialized job is green; missing reusable jobs and run attempts
must be visible. Successful focused dispatches cannot satisfy full-workflow
acceptance or enforced dependency-audit requirements.

### Required contexts need unambiguous producer coverage

The observed main branch metadata lists a generic required `gate` context.
The [coverage workflow][coverage] uses `jobs.gate`; the authority matcher uses
name and app ID. That is not sufficient vocabulary for describing every
underlying workflow/job/mode required by an acceptance plan.

GitHub [recommends unique job names across workflows][protected]. The #3664
supplement requests a context-to-workflow/job inventory and a staged migration,
not an immediate rename of live required checks. No branch-protection change
is authorized by this report. The same inventory should cover standalone,
caller and reusable concurrency namespaces; #3673 retains ownership of its
existing SBOM concurrency finding.

### Execution lifecycle needs definition before migration

#3658 proposes six execution statuses and forbids `ran=false` with `tool-error`.
It also needs to represent missing tools and process errors. Its implementation
must first decide whether `ran` means orchestration attempted, process started,
or target check executed. A failed spawn cannot require inventing a successful
process start, duration or exit code.

The #3658 supplement asks for an explicit lifecycle contract or a separate
producer-error envelope for observations that cannot honestly populate an
execution result. It does not silently change the proposed enum. Cancellation,
timeout, malformed output, missing capability and assertion failure need
separate observations and documented lossless mappings.

### Solo governance must reconcile policy sources

[AGENTS][agents] and [risk policy][risk] state that high-risk work requires at
least one human approval. #3667 proposes a solo topology with an explicit human
merge decision instead of inventing independent approval. The implementation
must reconcile declared profile, canonical policy and observed GitHub settings.
Historical shell output is not a fresh settings read; unavailable administration
metadata is unobserved, not an empty policy.

The #3667 supplement also separates stable decision material from mutable
observation metadata. Writing a final snapshot digest into a PR can trigger a
new check and change that snapshot. Reuse #3659's non-circular subject binding;
do not create an endless approval/capture loop or generate human decisions.

### Review convergence requires coverage, not an arbitrary cutoff

The #3661 supplement asks for one whole-diff baseline review, then delta reviews
of changed material and newly evidenced findings. Deduplicate repeated findings
by subject and preserve dispositions. A real new security or acceptance defect
remains actionable; no blanket P2 suppression or fixed maximum finding count is
proposed.

Regression matrices should cover adjacent failure paths together: discovery,
version probe, launch, timeout, parsing, command result, artifact handling and
finalization. Suggestions outside the declared scope are not automatically new
blocking requirements, but deferral and accepted-risk still follow policy and
human-decision rules.

## Recovery sequencing without a circular wait

The current #3658 recovery prerequisites remain in force. This report does not
accept a risk waiver or declare either recovery complete.

| Phase | Required evidence | Separately visible state |
| --- | --- | --- |
| #3672 candidate | Declared container runtime/build/export/scan/upload evidence and current required PR checks | #3671 dependency baseline remains unresolved |
| #3672 integration | Human regular merge and fresh main container evidence | Full security workflow may still fail for owned #3671 causes |
| #3671 combined candidate | Current main incorporated, dependency audits, SBOM concurrency, full enforced Security Analysis | Old successes do not substitute for the combined head |
| #3671 integration | Human regular merge and fresh main security/quality evidence | Any new or unclassified failure remains visible |
| #3658 start | Both recoveries accepted and a fresh scoped preflight | No automatic start from an unchanged snapshot |

Do not demand the aggregate result that #3671 must fix as a prerequisite for
implementing #3672, while simultaneously making #3671 wait for #3672. A known
baseline classification needs exact base SHA, workflow/job, failure fingerprint,
owner Issue and a review/expiry boundary. It remains a failure and cannot
satisfy a live required check or grant merge/release authorization.

## Parallel operation and validation cost

The [Context Pack][context] is design SSOT. The inspected [Boundary Map][map]
contains inventory and reservation example slices; a clean result for those
slices does not prove that two agents have disjoint runtime work assignments.
An execution plan should separately record operator, branch, worktree, target
paths, active CI and integration ownership.

Use focused tests while changing a bounded surface, then the declared full
exact-head acceptance suite for the final candidate. Do not repeatedly run all
heavy workflows for a formatting edit, but never reuse evidence whose relevant
subject, configuration or dependencies changed. External audit freshness must
be reevaluated; it is not guaranteed by an unchanged lockfile.

Use bounded polling with per-call timeouts, an overall deadline and rate-limit
handling. Cache immutable diagnostics rather than repeatedly fetching large
logs. Read-only observation should not comment, relabel, dispatch, cancel,
merge or close. Schedule independent acceptance runs serially when a shared
concurrency group would cancel them. Preserve failed and cancelled history.

Two independent runs support a declared reproducibility check; they are not a
universal minimum for every PR or proof over every future hosted runner image.
Record assigned images and observed versions without inferring unallocated
image coverage.

## Follow-up map

| Owner | Delivery | Scheduling boundary |
| --- | --- | --- |
| #3675 | This review report | Documentation only |
| #3676 | Authority subject binding, typed identities, bounded readers | Follow-up; not a new active recovery blocker |
| #3677 | Scoped acceptance and bounded observation | Preview/report-only first |
| #3658 | Execution lifecycle and status-preserving migration | Existing recovery prerequisites unchanged |
| #3661 | Review coverage, dispositions and delta convergence | Existing contract dependencies unchanged |
| #3664 | Actions trust, unique check mapping and concurrency inventory | Do not collide with active workflow fixes |
| #3667 | Solo profile and policy-source consistency | No automatic approval or settings mutation |

Existing #3631, #3632, #3638 and #3640 retain npm, Marketplace, root publication
boundary and consented pilot ownership. This report neither duplicates those
work items nor authorizes publication or external data collection.

## Validation and limitations

The deliverable is a new Markdown file only. Reviewed sources and follow-up
records are linked below. Local validation of the exact document bytes should
check YAML front matter, Markdown structure, references and whitespace.

No full repository test suite, dependency audit, hosted runtime reproduction,
formal verification, production implementation or publication was executed as
part of this review. Repository-wide `check:schemas`, `check:doc-consistency`
and `verify:lite` must be reported separately by the Draft PR's CI/operator.
A source review is not a cryptographic proof, an origin attestation or a claim
that all possible defects were inspected.

Context Pack conflict: none identified for this documentation-only addition.
No design object, morphism, acceptance test or production policy is changed.

## Source references

All repository source links below pin the inspected main commit. Issue and PR
links are navigation references whose current state may change.

[review]: https://github.com/itdojp/ae-framework/issues/3675
[binding]: https://github.com/itdojp/ae-framework/issues/3676
[acceptance]: https://github.com/itdojp/ae-framework/issues/3677
[product]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
[runbook]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/docs/integrations/CODEX-ISSUE-RUNBOOK.md
[authority]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/scripts/agents/github-work-state-lib.mjs
[stdio]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/scripts/codex/adapter-stdio.mjs
[capture]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/scripts/agents/capture-github-work-state.mjs
[coverage]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/.github/workflows/coverage-check.yml
[agents]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/AGENTS.md
[risk]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/policy/risk-policy.yml
[context]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/docs/spec/context-pack.md
[map]: https://github.com/itdojp/ae-framework/blob/c5da6115638fdbfeebbc458b39fa6916db66afb0/spec/context-pack/boundary-map.json
[protected]: https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches
