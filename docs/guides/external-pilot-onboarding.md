---
docRole: derived
canonicalSource:
- docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
- docs/product/EFFECTIVENESS-METRICS.md
- docs/ci/agent-pr-assurance-metrics.md
- docs/guides/byo-agent-assurance-onboarding.md
- docs/guides/byo-agent-assurance-quickstart.md
- docs/product/DOGFOODING-REPORT-2026Q3.md
lastVerified: '2026-06-23'
---

# External Pilot Onboarding Guide for Agent PR Assurance

> Language / 言語: English | 日本語

---

## English

Use this guide when an external repository wants to try ae-framework's
agent-assurance workflow without changing branch protection, introducing
auto-merge, or publishing sensitive PR data. The pilot starts **report-only**:
ae-framework produces reviewer-facing evidence and metrics, while maintainers
keep the release decision.

This guide is the consent-safe operating model for a minimal pilot: one
repository, about five pull requests, and a written agreement about what can be
collected, redacted, and later summarized in the ACP-097 external pilot report.
Use `docs/product/PILOT-RUNBOOK-2026Q3.md` and
`docs/product/PILOT-EVIDENCE-TEMPLATE.md` to execute and capture the pilot.

### 1. Purpose and non-goals

| Area | Pilot rule |
| --- | --- |
| Purpose | Show whether ae-framework's reviewer-first evidence surface helps maintainers inspect agent-generated or agent-reviewed PRs. |
| Default enforcement | Report-only. Do not add a new required check, branch-protection rule, or blocking policy for the pilot start. |
| Approval boundary | Producer output, metrics, and review-surface Markdown are evidence. They do not approve, merge, or replace maintainer judgment. |
| Auto-merge | Out of scope. The pilot must not enable or promise auto-merge. |
| Vendor comparison | Out of scope. Do not rank Codex, Claude Code, Copilot, or any other agent. |
| Strict gates | Out of scope for the default pilot. Do not require all PRs to run formal proof, heavy assurance lanes, or all-PR strict gates. |
| Publication | Only aggregated or redacted findings may be published, and only after the pilot maintainer approves the publication boundary. |

### 2. Pilot repository selection criteria

Choose a repository only when all of the following are true:

- The maintainer can identify roughly five upcoming PRs where reviewer feedback
  is useful and timing data is not operationally sensitive after aggregation.
- The repository has an ordinary CI baseline that can be observed without
  changing branch protection.
- The pilot maintainer can approve a redaction plan for PR titles, URLs,
  reviewer names, comments, file paths, and timing data.
- The PRs are small or medium in size; avoid incident response, security
  embargo, personnel, customer-data, or legal-contract changes.
- The team accepts that the first iteration is report-only and may end early if
  the review surface creates confusion or exposes sensitive information.

Do not start the pilot when the only available PRs are confidential incidents,
customer-specific fixes, unreleased business strategy, or compliance/legal work
that cannot be summarized safely.

### 3. Roles, permissions, and collected data

| Role | Responsibility | Minimum permission |
| --- | --- | --- |
| Pilot maintainer | Owns consent, repository selection, publication approval, and merge decisions. | Normal maintainer access to the target repository. |
| ae-framework operator | Runs the quickstart, metrics collector, and optional review-surface posting helper. | Local clone access; read access to the pilot PRs; optional comment permission only when posting a PR comment. |
| Reviewer | Reads the generated surface and leaves normal review feedback. | Existing reviewer permission in the target repository. |

The pilot may collect the following data for each PR:

- PR number or redacted identifier, title or redacted title, state, timestamps,
  merge timestamp, and optional review-ready timestamp.
- Required-check names, statuses, conclusions, and stale/superseded
  classification counts.
- Review-thread counts and final unresolved-thread count.
- Links or local paths to summary artifacts such as producer, assurance, policy,
  verify-lite, review-completeness, and metrics outputs.
- Maintainer disposition notes such as `merge`, `request changes`, `defer`, or
  `block` when the maintainer chooses to record them.

Raw review comments, reviewer identities, file paths, repository names, precise
wall-clock timing, and internal incident context are sensitive by default.

### 4. Consent and publication boundary

Before the first pilot PR, record this consent boundary in the repository Issue,
a private maintainer note, or another agreed location:

- Who can run the collector and who can see raw outputs.
- Whether live PR URLs may appear in private artifacts.
- Which fields must be redacted before sharing outside the pilot team.
- Whether aggregated counts may be used in the ACP-097 report.
- Whether a sanitized example PR can be described publicly.
- Who gives final approval before publication.

Publication-safe output should use one of these forms:

1. **Aggregate only** — publish counts and observations across about five PRs.
2. **Redacted case note** — replace repository name, PR URL, reviewer identity,
   comments, file paths, and exact timestamps with neutral identifiers.
3. **Synthetic fixture** — reproduce the learning with an offline fixture instead
   of a live PR.

If publication approval is unclear, keep the data private and mark the ACP-097
input as `not approved for publication`.

### 5. Setup sequence

Run the pilot in this order.

#### Step 1 — Quickstart

Start with the offline quickstart so maintainers see the evidence flow before a
live PR is touched:

```bash
pnpm run demo:agent-assurance
```

Open `artifacts/review/agent-assurance-demo/assurance-review.md` and confirm
that the reviewer surface is understandable. This step requires no GitHub token,
external LLM API, hosted agent service, or live PR.

#### Step 2 — Metrics collector

For each pilot PR, run the report-only metrics collector. Use fixture mode for a
sanitized dry run, or live mode when the maintainer has approved read access.
Before live collection, list the target repository's actual required-check names;
`gate`, `policy-gate`, and `verify-lite` are only ae-framework defaults. Pass
each target check with the repeatable `--required-check` option so CI/rerun
metrics reflect the pilot repository rather than this repository.

```bash
pnpm run metrics:agent-pr-assurance -- \
  --repo <owner/repo> \
  --pr <number> \
  --required-check "<target-required-check-1>" \
  --required-check "<target-required-check-2>" \
  --review-ready-at <iso-8601 timestamp if approved> \
  --output-json artifacts/metrics/pilot-pr-<redacted-id>.json \
  --output-md artifacts/metrics/pilot-pr-<redacted-id>.md
```

Keep optional fields as `not_collected` or `unknown` when they were not approved
or cannot be collected. If the pilot maintainer cannot confirm the required
check names, record required-check metrics as `not_collected` instead of using
ae-framework defaults. Do not replace missing data with zero.

#### Step 3 — Review surface posting

Use the generated metrics Markdown as the minimum report-only reviewer surface.
If the PR also has a full `assurance-review.md`, review that body instead.
Preview the selected body before posting anything:

```bash
pnpm run assurance:post-review-surface -- \
  --repo <owner/repo> \
  --pr <number> \
  --body-file artifacts/metrics/pilot-pr-<redacted-id>.md \
  --marker '<!-- ae-assurance-review-surface -->'
```

Only after the maintainer approves the body and `gh auth status` is confirmed,
switch to manual comment mode:

```bash
pnpm run assurance:post-review-surface -- \
  --repo <owner/repo> \
  --pr <number> \
  --body-file artifacts/metrics/pilot-pr-<redacted-id>.md \
  --mode comment \
  --marker '<!-- ae-assurance-review-surface -->'
```

The helper uses `gh pr comment`. It does not approve, review, merge, update
branch protection, or update an existing comment.

#### Step 4 — PR feedback

Reviewers use the posted or dry-run surface as a checklist before raw logs:

1. Check producer scope and missing-evidence findings.
2. Check required-check status and stale/superseded CI classification.
3. Check unresolved review-thread count and maintainer disposition.
4. Leave normal review comments or request changes through the existing PR
   workflow.
5. Record whether the surface was useful, confusing, incomplete, or too noisy.

### 6. Evidence checklist per pilot PR

Copy this checklist into the private pilot tracker or PR note for each PR:

- [ ] Maintainer consent for this PR is recorded.
- [ ] PR identifier is redacted or approved for private artifact use.
- [ ] Quickstart was shown before live data collection, or the maintainer waived
      that step.
- [ ] Metrics JSON and Markdown were generated in report-only mode.
- [ ] Review surface was previewed before posting.
- [ ] Posted PR comment URL is recorded, or posting was intentionally skipped.
- [ ] Target repository required-check names are recorded and captured without
      changing branch protection.
- [ ] Review-completeness status and unresolved-thread count are captured when
      available.
- [ ] Sensitive fields were reviewed for redaction before any sharing.
- [ ] Publication status is recorded as `approved`, `aggregate only`, `private`,
      or `not approved for publication`.

### 7. Redaction path

Before sending pilot data outside the pilot team:

1. Replace repository, organization, branch, PR, reviewer, and file-path names
   with neutral identifiers such as `repo-a`, `pr-1`, `reviewer-1`, and
   `path-redacted`.
2. Replace exact timestamps with durations or coarse date buckets when timing is
   approved for aggregation.
3. Summarize review comments by category instead of copying text.
4. Keep raw collector output private; publish only sanitized Markdown, aggregate
   tables, or synthetic fixtures.
5. Ask the pilot maintainer to approve the final redacted excerpt before it is
   used in the ACP-097 report, release notes, blog posts, or social posts.

### 8. Completion and abort criteria

A pilot is complete when:

- about five PRs have report-only metrics and reviewer-surface notes;
- each PR has a recorded publication status;
- maintainers can state whether the evidence surface clarified review,
  duplicated existing work, or created friction;
- the operator can summarize limitations and redaction decisions for ACP-097;
- no unresolved consent or publication question remains.

Abort or pause the pilot when:

- sensitive data appears in a surface that cannot be redacted safely;
- the surface is mistaken for an approval, auto-merge signal, or required gate;
- the pilot needs branch-protection changes before report-only learning is
  complete;
- reviewers cannot understand the evidence surface after one revision;
- maintainer consent, role ownership, or publication approval becomes unclear.

### 9. Connection to ACP-097

The ACP-097 external pilot report should reuse the metric vocabulary from
`docs/product/EFFECTIVENESS-METRICS.md`, the runbook fields from
`docs/product/PILOT-RUNBOOK-2026Q3.md`, and the template fields from
`docs/product/PILOT-EVIDENCE-TEMPLATE.md`. Include only approved data:

- pilot scope: repository type, PR count, and selected PR categories;
- report-only setup: commands used, posted surfaces, and skipped permissions;
- metric summary: review-thread counts, unresolved-thread final counts,
  required-check classifications, `ci_rerun_count`, and timing metrics when
  approved;
- reviewer feedback: useful, missing, confusing, and noisy parts of the surface;
- privacy outcome: aggregate-only, redacted case note, synthetic fixture, or
  private-only decision;
- limitations: no auto-merge, no vendor ranking, no all-PR strict gate, and no
  causal speed claim without controlled baseline.

---

## 日本語

このガイドは、外部 repository が branch protection 変更、auto-merge、有感な PR data の公開を行わずに、ae-framework の agent-assurance workflow を試すための手順です。Pilot は **report-only** で開始します。ae-framework は reviewer 向け evidence と metrics を作成しますが、release decision は maintainer が保持します。

このガイドは、最小 pilot（1 repository / おおよそ 5 PR）の consent-safe operating model です。何を収集し、何を redact し、後続の ACP-097 external pilot report に何を要約できるかを事前に合意します。実行と記録には `docs/product/PILOT-RUNBOOK-2026Q3.md` と `docs/product/PILOT-EVIDENCE-TEMPLATE.md` を使います。

### 1. 目的と非目的

| 領域 | Pilot rule |
| --- | --- |
| 目的 | ae-framework の reviewer-first evidence surface が、agent-generated / agent-reviewed PR の確認に役立つかを確認する。 |
| 既定の enforcement | Report-only。開始時点では required check、branch-protection rule、blocking policy を追加しない。 |
| Approval boundary | Producer output、metrics、review-surface Markdown は evidence であり、approve / merge / maintainer judgment の代替ではない。 |
| Auto-merge | 対象外。Pilot で auto-merge を有効化または約束しない。 |
| Vendor comparison | 対象外。Codex、Claude Code、Copilot、その他 agent を順位付けしない。 |
| Strict gates | 既定 pilot では対象外。全 PR に formal proof、heavy assurance lane、all-PR strict gate を要求しない。 |
| Publication | 公開できるのは、pilot maintainer が承認した boundary 内の集約値または redact 済み情報のみ。 |

### 2. Pilot repository selection criteria

次をすべて満たす repository だけを選びます。

- Maintainer が、reviewer feedback を得る価値があり、集約後の timing data が運用上の秘密にならない PR をおおよそ 5 件選べる。
- Branch protection を変更せずに観測できる通常の CI baseline がある。
- PR title、URL、reviewer name、comment、file path、timing data の redaction plan を maintainer が承認できる。
- PR は小〜中規模である。Incident response、security embargo、人事、customer-data、legal-contract 変更は避ける。
- 初回 iteration が report-only であり、surface が混乱や機微情報露出を起こす場合は早期終了できることを team が受け入れる。

Confidential incident、顧客固有修正、未公開事業戦略、compliance / legal work しか対象がない場合は、pilot を開始しません。

### 3. 役割、権限、収集 data

| Role | Responsibility | Minimum permission |
| --- | --- | --- |
| Pilot maintainer | Consent、repository selection、publication approval、merge decision を所有する。 | 対象 repository の通常 maintainer access。 |
| ae-framework operator | Quickstart、metrics collector、任意の review-surface posting helper を実行する。 | Local clone access、pilot PR の read access、PR comment を投稿する場合だけ comment permission。 |
| Reviewer | 生成された surface を読み、通常の review feedback を残す。 | 対象 repository の既存 reviewer permission。 |

PR ごとに収集し得る data は次です。

- PR number または redacted identifier、title または redacted title、state、timestamp、merge timestamp、任意の review-ready timestamp。
- Required check の name、status、conclusion、stale / superseded classification count。
- Review-thread count と final unresolved-thread count。
- Producer、assurance、policy、verify-lite、review-completeness、metrics output などの summary artifact link / local path。
- Maintainer が記録する場合の `merge`、`request changes`、`defer`、`block` などの disposition note。

Raw review comment、reviewer identity、file path、repository name、正確な wall-clock timing、internal incident context は既定で sensitive と扱います。

### 4. Consent と publication boundary

最初の pilot PR の前に、次の consent boundary を repository Issue、private maintainer note、または合意済みの場所に記録します。

- Collector を実行できる人と raw output を見られる人。
- Live PR URL を private artifact に含めてよいか。
- Pilot team 外へ共有する前に redaction が必要な field。
- Aggregated count を ACP-097 report に使ってよいか。
- Sanitized example PR を public に説明してよいか。
- Publication 前の final approval owner。

公開に適した output は次のいずれかです。

1. **Aggregate only** — おおよそ 5 PR の count と観測結果だけを公開する。
2. **Redacted case note** — repository name、PR URL、reviewer identity、comment、file path、exact timestamp を neutral identifier に置き換える。
3. **Synthetic fixture** — live PR ではなく offline fixture で学習内容を再現する。

公開承認が不明な場合は data を private に留め、ACP-097 input は `not approved for publication` と記録します。

### 5. Setup sequence

Pilot は次の順で実行します。

#### Step 1 — Quickstart

Live PR に触れる前に offline quickstart を実行し、maintainer に evidence flow を見せます。

```bash
pnpm run demo:agent-assurance
```

`artifacts/review/agent-assurance-demo/assurance-review.md` を開き、reviewer surface が理解できるか確認します。この step は GitHub token、外部 LLM API、hosted agent service、live PR を必要としません。

#### Step 2 — Metrics collector

Pilot PR ごとに report-only metrics collector を実行します。Sanitized dry run では fixture mode、maintainer が read access を承認した場合は live mode を使います。Live collection 前に target repository の実際の required-check name を列挙します。`gate`、`policy-gate`、`verify-lite` は ae-framework の既定値にすぎません。Pilot repository の CI / rerun metrics になるよう、repeatable な `--required-check` で target check をそれぞれ指定します。

```bash
pnpm run metrics:agent-pr-assurance -- \
  --repo <owner/repo> \
  --pr <number> \
  --required-check "<target-required-check-1>" \
  --required-check "<target-required-check-2>" \
  --review-ready-at <iso-8601 timestamp if approved> \
  --output-json artifacts/metrics/pilot-pr-<redacted-id>.json \
  --output-md artifacts/metrics/pilot-pr-<redacted-id>.md
```

承認されていない、または収集できない任意 field は `not_collected` / `unknown` のままにします。Pilot maintainer が required-check name を確認できない場合は、ae-framework default を使わず、required-check metrics を `not_collected` として記録します。欠測を 0 として扱いません。

#### Step 3 — Review surface posting

最小の report-only reviewer surface として、生成した metrics Markdown を使います。PR に full
`assurance-review.md` がある場合は、その本文を確認して使います。投稿前に、選択した本文を必ず preview します。

```bash
pnpm run assurance:post-review-surface -- \
  --repo <owner/repo> \
  --pr <number> \
  --body-file artifacts/metrics/pilot-pr-<redacted-id>.md \
  --marker '<!-- ae-assurance-review-surface -->'
```

Maintainer が本文を承認し、`gh auth status` を確認した後でのみ、manual comment mode に切り替えます。

```bash
pnpm run assurance:post-review-surface -- \
  --repo <owner/repo> \
  --pr <number> \
  --body-file artifacts/metrics/pilot-pr-<redacted-id>.md \
  --mode comment \
  --marker '<!-- ae-assurance-review-surface -->'
```

この helper は `gh pr comment` を使います。approve、review、merge、branch protection 更新、既存 comment 更新は行いません。

#### Step 4 — PR feedback

Reviewer は raw log より先に、投稿済みまたは dry-run の surface を checklist として使います。

1. Producer scope と missing-evidence finding を確認する。
2. Required-check status と stale / superseded CI classification を確認する。
3. Unresolved review-thread count と maintainer disposition を確認する。
4. 既存の PR workflow で通常の review comment または changes request を残す。
5. Surface が有用、混乱、不完全、過剰ノイズのどれだったかを記録する。

### 6. Pilot PR ごとの evidence checklist

各 PR で次の checklist を private pilot tracker または PR note にコピーします。

- [ ] この PR の maintainer consent を記録した。
- [ ] PR identifier は redacted 済み、または private artifact 利用が承認済みである。
- [ ] Live data collection 前に quickstart を見せた、または maintainer が waive した。
- [ ] Metrics JSON / Markdown を report-only mode で生成した。
- [ ] 投稿前に review surface を preview した。
- [ ] Posted PR comment URL を記録した、または投稿しない判断を記録した。
- [ ] Target repository の required-check name を記録し、branch protection を変更せず取得した。
- [ ] 利用可能な場合、review-completeness status と unresolved-thread count を取得した。
- [ ] 共有前に sensitive field の redaction を確認した。
- [ ] Publication status を `approved`、`aggregate only`、`private`、または `not approved for publication` として記録した。

### 7. Redaction path

Pilot team 外へ data を出す前に、次を行います。

1. Repository、organization、branch、PR、reviewer、file path 名を `repo-a`、`pr-1`、`reviewer-1`、`path-redacted` などの neutral identifier に置き換える。
2. Timing の集約が承認されている場合でも、exact timestamp は duration または粗い日付 bucket に置き換える。
3. Review comment は原文コピーではなく category で要約する。
4. Raw collector output は private に保持し、公開するのは sanitized Markdown、aggregate table、synthetic fixture に限定する。
5. ACP-097 report、release note、blog、SNS post に使う前に、pilot maintainer が最終 redacted excerpt を承認する。

### 8. Completion / abort criteria

Pilot は次を満たすと完了です。

- おおよそ 5 PR に report-only metrics と reviewer-surface note がある。
- 各 PR の publication status が記録されている。
- Maintainer が evidence surface について、review を明確にした、既存作業と重複した、または friction を生んだ、のいずれかを述べられる。
- Operator が ACP-097 向けに limitation と redaction decision を要約できる。
- Consent または publication に関する未解決の問いがない。

次の場合は pilot を中止または一時停止します。

- Surface に sensitive data が出て、安全に redact できない。
- Surface が approval、auto-merge signal、required gate と誤解される。
- Report-only learning 完了前に branch-protection 変更が必要になる。
- 1回修正しても reviewer が evidence surface を理解できない。
- Maintainer consent、role ownership、publication approval が不明確になる。

### 9. ACP-097 への接続

ACP-097 external pilot report は `docs/product/EFFECTIVENESS-METRICS.md` の metric vocabulary、`docs/product/PILOT-RUNBOOK-2026Q3.md` の runbook field、`docs/product/PILOT-EVIDENCE-TEMPLATE.md` の template field を再利用し、承認済み data のみを含めます。

- pilot scope: repository type、PR count、selected PR category。
- report-only setup: 使用 command、posted surface、skipped permission。
- metric summary: review-thread count、final unresolved-thread count、required-check classification、`ci_rerun_count`、承認された timing metrics。
- reviewer feedback: surface の useful / missing / confusing / noisy な点。
- privacy outcome: aggregate-only、redacted case note、synthetic fixture、private-only decision。
- limitation: auto-merge なし、vendor ranking なし、all-PR strict gate なし、controlled baseline なしの causal speed claim なし。
