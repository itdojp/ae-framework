---
docRole: derived
canonicalSource:
- docs/ci-policy.md
- docs/ci/OPT-IN-CONTROLS.md
- policy/risk-policy.yml
- docs/ci/branch-protection-operations.md
lastVerified: '2026-03-31'
---

# Recipe: Quality Profile

> 🌍 Language / 言語: English | 日本語

---

## English

### When to use
- when you need to decide which heavy validation lanes should run for the current PR
- when you need to justify strict review, security, or other opt-in checks from the diff and risk posture
- when you need a short operator path from PR labels to the expected required and non-required checks

### What to load (primary sources)
- `docs/ci-policy.md`
- `docs/ci/OPT-IN-CONTROLS.md`
- `policy/risk-policy.yml`
- `docs/ci/branch-protection-operations.md`

### Commands (copy/paste)
Start by reading the current PR surface, then apply only the lanes you can justify from the change scope and policy.

```bash no-doctest
gh pr view <PR_NUMBER> --json labels,files
```

```bash no-doctest
gh pr comment <PR_NUMBER> --body '/review strict'
```

```bash no-doctest
gh pr comment <PR_NUMBER> --body '/run-security'
```

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

### Expected output
- labels and dispatch requests are selected from the actual change scope rather than habit
- required checks stay aligned with branch protection while optional heavy lanes remain explainable
- the PR record shows why a stricter lane was added or intentionally omitted

### Artifacts to check
- PR label history and timeline events
- `policy-gate` summaries and required-check URLs
- security / coverage / heavy-lane job logs that were explicitly requested

### First checks to perform
- confirm which files changed before adding any heavy lane; do not infer security or strict review needs from PR title alone
- compare requested labels with `policy/risk-policy.yml` so the PR does not carry stricter lanes without a documented rationale
- if a requested lane did not start, verify whether the triggering event and branch freshness actually changed after the label or slash command

### Follow-up
- remove unnecessary heavy lanes when they no longer match the actual risk or file scope
- keep required lanes when policy or branch protection still demands them, and record the reason directly in the PR
- escalate to `docs/ci/OPT-IN-CONTROLS.md` or `docs/ci/branch-protection-operations.md` when the behavior differs from the expected trigger model

## 日本語

### When to use
- 現在の PR で、どの heavy validation lane を起動すべきか判断したいとき
- diff と risk posture に基づいて strict review、security などの opt-in check の必要性を説明したいとき
- PR labels から expected required / non-required checks までを短い手順で確認したいとき

### What to load (primary sources)
- `docs/ci-policy.md`
- `docs/ci/OPT-IN-CONTROLS.md`
- `policy/risk-policy.yml`
- `docs/ci/branch-protection-operations.md`

### Commands (copy/paste)
まず現在の PR surface を確認し、その後で変更範囲と policy に基づいて必要な lane だけを起動します。

```bash no-doctest
gh pr view <PR_NUMBER> --json labels,files
```

```bash no-doctest
gh pr comment <PR_NUMBER> --body '/review strict'
```

```bash no-doctest
gh pr comment <PR_NUMBER> --body '/run-security'
```

```bash no-doctest
gh pr checks <PR_NUMBER> --required
```

### Expected output
- labels と dispatch request を、慣例ではなく実際の変更範囲に基づいて選択できる
- required checks は branch protection と整合し、optional な heavy lane も理由付きで説明できる
- なぜ stricter lane を追加したか、あるいは追加しなかったかを PR 上に記録できる

### Artifacts to check
- PR の label history と timeline events
- `policy-gate` summary と required-check URL
- 明示的に要求した security / coverage / heavy-lane job log

### First checks to perform
- heavy lane を追加する前に、まず変更ファイルを確認する。PR title だけで security や strict review の必要性を推定しない
- 要求した label が `policy/risk-policy.yml` と整合しているか確認し、根拠のない stricter lane を持ち込まない
- 要求した lane が起動しない場合は、label や slash command の後に trigger event と branch freshness が変化しているかを確認する

### Follow-up
- 実際の risk や file scope と一致しなくなった heavy lane は解除する
- policy や branch protection が required lane を要求する場合は維持し、その理由を PR に直接記録する
- 期待した trigger model と挙動が異なる場合は `docs/ci/OPT-IN-CONTROLS.md` または `docs/ci/branch-protection-operations.md` へ escalation する
