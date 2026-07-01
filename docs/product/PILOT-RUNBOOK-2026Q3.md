---
docRole: derived
canonicalSource:
- docs/guides/external-pilot-onboarding.md
- docs/product/EFFECTIVENESS-METRICS.md
- docs/ci/agent-pr-assurance-metrics.md
- docs/guides/byo-agent-assurance-quickstart.md
lastVerified: '2026-06-23'
owner: product-assurance
verificationCommand: pnpm -s run check:doc-consistency
---

# Pilot Runbook 2026 Q3: Report-Only External Agent PR Assurance

> Language / 言語: English | 日本語

---

## English

This runbook prepares the first report-only external pilot for ae-framework's
agent PR assurance workflow. It is **pilot-ready**, not a completed public pilot
report. As of 2026-06-23, no external repository pilot result is recorded in
this document.

Use this runbook with `docs/product/LIVE-PILOT-ENTRY-CRITERIA.md`,
`docs/guides/external-pilot-onboarding.md`, and the per-PR evidence fields from
`docs/product/PILOT-EVIDENCE-TEMPLATE.md`. The live-pilot entry criteria decide
whether collection may start and what claim boundaries remain unsupported.

### 1. Pilot scope and non-goals

| Item | Operating rule |
| --- | --- |
| Pilot size | One repository and about five pull requests. |
| Mode | Report-only. Do not change branch protection, required checks, or merge policy. |
| Reviewer workflow | The generated surface supports normal review; it does not replace review, approval, request-changes, or merge decisions. |
| Publication | Use only maintainer-approved aggregate or redacted data. Keep raw outputs private by default. |
| Non-goals | No auto-merge, no agent-vendor ranking, no all-PR strict gate, no adoption-speed claim without a controlled baseline. |
| If a live pilot is unavailable | Complete the pilot-ready checklist and use the synthetic placeholder example under `examples/pilot-redacted/`. |

### 2. Roles and consent gate

Do not collect live PR data until these roles and decisions are recorded:

- **Pilot maintainer** — approves repository selection, consent, redaction,
  publication status, and merge decisions.
- **ae-framework operator** — runs local commands and captures report-only
  evidence.
- **Reviewer** — uses the surface as support for normal review feedback.

Required consent decisions:

- who can see raw outputs;
- whether PR URLs may appear in private artifacts;
- which fields must be redacted before any sharing;
- whether aggregate counts can feed ACP-097;
- whether a redacted case note can be published;
- who signs off before publication.

### 3. Pilot-ready checklist

- [ ] Pilot maintainer and operator are named.
- [ ] Target repository is selected and unsuitable PR categories are excluded.
- [ ] Five candidate PR slots are identified, or placeholder slots are created.
- [ ] Actual target-repository required-check names are listed.
- [ ] Publication status vocabulary is agreed: `approved`, `aggregate only`,
      `private`, or `not approved for publication`.
- [ ] Redaction rules cover repository name, PR URL, reviewer identity, comments,
      file paths, exact timestamps, and sensitive business context.
- [ ] Bash and PowerShell command paths are validated in a local dry run.
- [ ] Abort criteria are accepted before the first live PR.

### 4. Per-PR execution flow

Repeat this flow for each of the five pilot PRs.

1. **Register the PR slot.** Assign a redacted ID such as `pilot-pr-1` and copy
   one row from `docs/product/PILOT-EVIDENCE-TEMPLATE.md`.
2. **Confirm required checks.** Capture the target repository's real required
   check names. Do not use ae-framework defaults unless the pilot repository uses
   those exact names.
3. **Run the metrics collector.** Generate report-only JSON and Markdown.
4. **Preview the review surface.** Use the metrics Markdown as the minimum body,
   or use a full reviewer Markdown surface such as
   `examples/pilot-redacted/review-surface.example.md` when the pilot PR has one.
5. **Post only with approval.** Use `--mode comment` only after the maintainer
   approves the body and the operator verifies `gh auth status`.
6. **Capture reviewer disposition.** Record `merge`, `request changes`, `defer`,
   `block`, or `not collected`.
7. **Redact before sharing.** Convert live identifiers to the evidence template
   vocabulary before sending data outside the pilot team.

### 5. Bash commands

Set variables once per PR:

```bash
REPO="owner/repo"
PR="123"
PILOT_ID="pilot-pr-1"
OUT="artifacts/metrics/${PILOT_ID}"
mkdir -p "$OUT"
```

Run the collector with the target repository's actual required checks:

```bash
pnpm run metrics:agent-pr-assurance -- \
  --repo "$REPO" \
  --pr "$PR" \
  --required-check "<target-required-check-1>" \
  --required-check "<target-required-check-2>" \
  --review-ready-at "<iso-8601 timestamp if approved>" \
  --output-json "$OUT/agent-pr-assurance-metrics.json" \
  --output-md "$OUT/agent-pr-assurance-metrics.md"
```

Preview the PR comment body without posting:

```bash
pnpm run assurance:post-review-surface -- \
  --repo "$REPO" \
  --pr "$PR" \
  --body-file "$OUT/agent-pr-assurance-metrics.md" \
  --marker '<!-- ae-assurance-review-surface -->'
```

Post only after approval:

```bash
gh auth status
pnpm run assurance:post-review-surface -- \
  --repo "$REPO" \
  --pr "$PR" \
  --body-file "$OUT/agent-pr-assurance-metrics.md" \
  --mode comment \
  --marker '<!-- ae-assurance-review-surface -->'
```

### 6. PowerShell commands

Set variables once per PR:

```powershell
$Repo = "owner/repo"
$Pr = "123"
$PilotId = "pilot-pr-1"
$Out = "artifacts/metrics/$PilotId"
New-Item -ItemType Directory -Force -Path $Out | Out-Null
```

Run the collector with the target repository's actual required checks:

```powershell
pnpm run metrics:agent-pr-assurance -- `
  --repo $Repo `
  --pr $Pr `
  --required-check "<target-required-check-1>" `
  --required-check "<target-required-check-2>" `
  --review-ready-at "<iso-8601 timestamp if approved>" `
  --output-json "$Out/agent-pr-assurance-metrics.json" `
  --output-md "$Out/agent-pr-assurance-metrics.md"
```

Preview the PR comment body without posting:

```powershell
pnpm run assurance:post-review-surface -- `
  --repo $Repo `
  --pr $Pr `
  --body-file "$Out/agent-pr-assurance-metrics.md" `
  --marker '<!-- ae-assurance-review-surface -->'
```

Post only after approval:

```powershell
gh auth status
pnpm run assurance:post-review-surface -- `
  --repo $Repo `
  --pr $Pr `
  --body-file "$Out/agent-pr-assurance-metrics.md" `
  --mode comment `
  --marker '<!-- ae-assurance-review-surface -->'
```

### 7. Evidence capture fields for five PRs

Use one row per PR. The required fields are defined in
`docs/product/PILOT-EVIDENCE-TEMPLATE.md` and mirrored by
`examples/pilot-redacted/pilot-evidence-log.example.csv`:

| Field | Required meaning |
| --- | --- |
| `pilot_pr_id` | Redacted ID such as `pilot-pr-1`; do not expose the live PR number publicly unless approved. |
| `producer` | Agent, human, CI, formal tool, or mixed producer source. |
| `issue_scope` | Redacted Issue or change scope. |
| `review_surface_link` | Private PR comment URL, local Markdown path, or `not posted`. |
| `metrics_json` | Path to the collector JSON or `not_collected`. |
| `reviewer_disposition` | `merge`, `request changes`, `defer`, `block`, or `not_collected`. |
| `limitations` | Missing data, noisy fields, stale checks, reviewer feedback, or redaction constraints. |
| `publication_status` | `approved`, `aggregate only`, `private`, or `not approved for publication`. |

### 8. Abort criteria

Abort or pause the pilot when any of the following occur:

- CI is unstable enough that required-check metrics cannot be interpreted.
- Required-check names cannot be confirmed and the maintainer needs current CI
  metrics for the pilot decision.
- Maintainer consent, role ownership, or publication approval is missing.
- Data cannot be redacted without exposing sensitive repository, reviewer,
  customer, incident, or business context.
- The review surface is mistaken for approval, auto-merge, or a required gate.
- Reviewers report that the surface is confusing after one revision.
- The pilot would require branch-protection or blocking-gate changes before
  report-only learning is complete.

### 9. Placeholder report for ACP-097

If the live pilot is not yet executed, ACP-097 should use this placeholder status
instead of implying completion:

```text
Status: pilot-ready, not executed
Repository: not selected or redacted
PR count: 0 live PRs collected / 5 planned
Evidence: runbook, evidence template, and synthetic redacted example only
Publication: not approved for publication until maintainer sign-off
Claims allowed: readiness only; no adoption-speed, quality, or vendor comparison claim
```

---

## 日本語

この runbook は、ae-framework の agent PR assurance workflow を最初の外部 repository pilot で report-only に試すための準備手順です。これは **pilot-ready** な手順であり、完了済みの公開 pilot report ではありません。2026-06-23 時点で、この文書には外部 repository pilot の実績値を記録していません。

`docs/guides/external-pilot-onboarding.md` と併用し、PR ごとの evidence field は `docs/product/PILOT-EVIDENCE-TEMPLATE.md` からコピーします。

### 1. Pilot scope と非目的

| Item | Operating rule |
| --- | --- |
| Pilot size | 1 repository / おおよそ 5 pull requests。 |
| Mode | Report-only。branch protection、required checks、merge policy は変更しない。 |
| Reviewer workflow | 生成 surface は通常 review を支援する。review、approval、request changes、merge decision を置き換えない。 |
| Publication | maintainer 承認済みの aggregate または redacted data だけを使う。raw output は既定で private。 |
| Non-goals | auto-merge、agent vendor ranking、all-PR strict gate、controlled baseline のない adoption-speed claim は対象外。 |
| Live pilot がない場合 | pilot-ready checklist を完了し、`examples/pilot-redacted/` の synthetic placeholder example を使う。 |

### 2. Roles と consent gate

Live PR data を収集する前に、次を記録します。

- **Pilot maintainer** — repository selection、consent、redaction、publication status、merge decision を承認する。
- **ae-framework operator** — local command を実行し、report-only evidence を取得する。
- **Reviewer** — surface を通常 review feedback の補助として使う。

Required consent decisions:

- raw output を見られる人。
- PR URL を private artifact に含めてよいか。
- 共有前に redaction が必要な field。
- aggregate count を ACP-097 に渡せるか。
- redacted case note を公開できるか。
- publication 前の sign-off owner。

### 3. Pilot-ready checklist

- [ ] Pilot maintainer と operator を記名した。
- [ ] Target repository を選定し、不適切な PR category を除外した。
- [ ] 5件の candidate PR slot、または placeholder slot を作成した。
- [ ] Target repository の actual required-check name を列挙した。
- [ ] Publication status vocabulary を合意した: `approved`、`aggregate only`、`private`、`not approved for publication`。
- [ ] Redaction rules が repository name、PR URL、reviewer identity、comment、file path、exact timestamp、sensitive business context を覆っている。
- [ ] Bash / PowerShell command path を local dry run で確認した。
- [ ] 最初の live PR 前に abort criteria を合意した。

### 4. PR ごとの実行 flow

5件の pilot PR それぞれで、この flow を繰り返します。

1. **PR slot を登録する。** `pilot-pr-1` のような redacted ID を割り当て、`docs/product/PILOT-EVIDENCE-TEMPLATE.md` から 1 行コピーする。
2. **Required checks を確認する。** Target repository の実際の required check name を取得する。Pilot repository が同じ名称を使う場合以外、ae-framework default は使わない。
3. **Metrics collector を実行する。** Report-only JSON / Markdown を生成する。
4. **Review surface を preview する。** 最小 body は metrics Markdown。pilot PR に full reviewer Markdown surface がある場合は、`examples/pilot-redacted/review-surface.example.md` のような実在 path を指定する。
5. **承認後だけ投稿する。** maintainer が body を承認し、operator が `gh auth status` を確認した後にのみ `--mode comment` を使う。
6. **Reviewer disposition を記録する。** `merge`、`request changes`、`defer`、`block`、または `not collected` を記録する。
7. **共有前に redact する。** pilot team 外へ送る前に live identifier を evidence template vocabulary へ変換する。

### 5. Bash commands

PR ごとに変数を設定します。

```bash
REPO="owner/repo"
PR="123"
PILOT_ID="pilot-pr-1"
OUT="artifacts/metrics/${PILOT_ID}"
mkdir -p "$OUT"
```

Target repository の actual required checks を指定して collector を実行します。

```bash
pnpm run metrics:agent-pr-assurance -- \
  --repo "$REPO" \
  --pr "$PR" \
  --required-check "<target-required-check-1>" \
  --required-check "<target-required-check-2>" \
  --review-ready-at "<iso-8601 timestamp if approved>" \
  --output-json "$OUT/agent-pr-assurance-metrics.json" \
  --output-md "$OUT/agent-pr-assurance-metrics.md"
```

投稿せずに PR comment body を preview します。

```bash
pnpm run assurance:post-review-surface -- \
  --repo "$REPO" \
  --pr "$PR" \
  --body-file "$OUT/agent-pr-assurance-metrics.md" \
  --marker '<!-- ae-assurance-review-surface -->'
```

承認後だけ投稿します。

```bash
gh auth status
pnpm run assurance:post-review-surface -- \
  --repo "$REPO" \
  --pr "$PR" \
  --body-file "$OUT/agent-pr-assurance-metrics.md" \
  --mode comment \
  --marker '<!-- ae-assurance-review-surface -->'
```

### 6. PowerShell commands

PR ごとに変数を設定します。

```powershell
$Repo = "owner/repo"
$Pr = "123"
$PilotId = "pilot-pr-1"
$Out = "artifacts/metrics/$PilotId"
New-Item -ItemType Directory -Force -Path $Out | Out-Null
```

Target repository の actual required checks を指定して collector を実行します。

```powershell
pnpm run metrics:agent-pr-assurance -- `
  --repo $Repo `
  --pr $Pr `
  --required-check "<target-required-check-1>" `
  --required-check "<target-required-check-2>" `
  --review-ready-at "<iso-8601 timestamp if approved>" `
  --output-json "$Out/agent-pr-assurance-metrics.json" `
  --output-md "$Out/agent-pr-assurance-metrics.md"
```

投稿せずに PR comment body を preview します。

```powershell
pnpm run assurance:post-review-surface -- `
  --repo $Repo `
  --pr $Pr `
  --body-file "$Out/agent-pr-assurance-metrics.md" `
  --marker '<!-- ae-assurance-review-surface -->'
```

承認後だけ投稿します。

```powershell
gh auth status
pnpm run assurance:post-review-surface -- `
  --repo $Repo `
  --pr $Pr `
  --body-file "$Out/agent-pr-assurance-metrics.md" `
  --mode comment `
  --marker '<!-- ae-assurance-review-surface -->'
```

### 7. 5 PR 分の evidence capture fields

`docs/product/PILOT-EVIDENCE-TEMPLATE.md` の field を PR ごとに 1 行使います。`examples/pilot-redacted/pilot-evidence-log.example.csv` も同じ構造です。

| Field | Required meaning |
| --- | --- |
| `pilot_pr_id` | `pilot-pr-1` のような redacted ID。承認がない限り live PR number は公開しない。 |
| `producer` | Agent、human、CI、formal tool、または mixed producer source。 |
| `issue_scope` | Redacted Issue または change scope。 |
| `review_surface_link` | Private PR comment URL、local Markdown path、または `not posted`。 |
| `metrics_json` | Collector JSON path、または `not_collected`。 |
| `reviewer_disposition` | `merge`、`request changes`、`defer`、`block`、または `not_collected`。 |
| `limitations` | Missing data、noisy fields、stale checks、reviewer feedback、redaction constraints。 |
| `publication_status` | `approved`、`aggregate only`、`private`、または `not approved for publication`。 |

### 8. Abort criteria

次のいずれかに該当する場合は pilot を中止または一時停止します。

- CI が不安定で required-check metrics を解釈できない。
- Required-check name を確認できず、maintainer が current CI metrics を pilot decision に必要としている。
- Maintainer consent、role ownership、publication approval がない。
- Repository、reviewer、customer、incident、business context の sensitive data を安全に redact できない。
- Review surface が approval、auto-merge、required gate と誤解される。
- 1 回修正しても reviewer が surface を混乱すると報告する。
- Report-only learning 完了前に branch protection または blocking gate の変更が必要になる。

### 9. ACP-097 用 placeholder report

Live pilot が未実施の場合、ACP-097 では完了済みのように見せず、次の placeholder status を使います。

```text
Status: pilot-ready, not executed
Repository: not selected or redacted
PR count: 0 live PRs collected / 5 planned
Evidence: runbook, evidence template, and synthetic redacted example only
Publication: not approved for publication until maintainer sign-off
Claims allowed: readiness only; no adoption-speed, quality, or vendor comparison claim
```
