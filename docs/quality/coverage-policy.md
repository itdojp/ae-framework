---
docRole: derived
canonicalSource:
- policy/quality.json
- docs/quality/verification-gates.md
lastVerified: '2026-07-02'
---
# Coverage Policy — Proposal and Operations

> Language / 言語: English | 日本語

---

## English

### Goals
- Keep PR handling fast and report-only by default.
- Escalate to blocking coverage checks only when operators or branch policy explicitly request it.
- Allow the `main` branch to enforce thresholds through a ratcheted baseline without losing the long-term `80%` target.

### Mechanics

Threshold source order:
1. PR label `coverage:<pct>` such as `coverage:75`
2. Emergency repository variable `COVERAGE_RATCHET_THRESHOLD` can override the checked-in `main` ratchet threshold when explicitly needed
3. On enforced `main` pushes, `configs/coverage-ratchet.json.mainThreshold` capped by the target threshold
4. Repository variable `COVERAGE_DEFAULT_THRESHOLD` with default `80`

Label parsing rules:
- in `.github/workflows/coverage-check.yml`, the first label whose text starts with lowercase `coverage:` wins
- the suffix after `coverage:` is passed directly to JavaScript `Number(...)`
- the gate workflow does not add extra trimming, case-folding, or range validation beyond that conversion
- `scripts/coverage/pr-coverage-summary.mjs` normalizes labels more aggressively for comment rendering, so gate behavior should be treated as authoritative when they differ

Blocking enforcement is enabled when:
- the PR has the `enforce-coverage` label, or
- the workflow runs on a push to `main` and repository variable `COVERAGE_ENFORCE_MAIN=1`, or
- an operator manually triggers `coverage-check` via `workflow_dispatch` with input `strict=true`; this is a manual override path rather than the normal PR policy

Reporting behavior:
- `.github/workflows/coverage-check.yml` posts a non-blocking PR comment that records effective coverage, effective threshold, threshold source, and current policy state
- Verify Lite logs note the current `COVERAGE_ENFORCE_MAIN` setting and the configured default threshold; they do not compute or print the effective threshold

### Main Ratchet Toward 80%
- The long-term target remains `80%` line coverage.
- `configs/coverage-ratchet.json` records the current enforceable `main` threshold and the observed evidence used to set it.
- As of run `28600653332` on 2026-07-02, the observed `main` line coverage was `36.18%`; the initial ratchet threshold is therefore `36.18%`.
- Raise `configs/coverage-ratchet.json.mainThreshold` in small increments after `main` remains green at the current threshold. The checked-in `minimumStep` documents the preferred minimum increase.
- Do not lower the ratchet threshold except as an explicit incident rollback with rationale, evidence, and a follow-up owner.

### Baseline Freshness and Generated Artifacts
- `pnpm run coverage` is the canonical project command for generating local coverage evidence.
- The command writes `coverage/coverage-summary.json` and `coverage/lcov.info`; `coverage/` is ignored by `.gitignore` and is treated as generated evidence, not as a manually maintained tracked baseline.
- When documenting a baseline, record the target commit, command, date, and relevant environment flags. Do not infer freshness from an old local `coverage/` directory alone.
- `pnpm run coverage:freshness` reads `coverage/coverage-summary.json` and writes report-only freshness evidence to `artifacts/testing/coverage-freshness.json` and `artifacts/testing/coverage-freshness.md`.
- Freshness statuses are `fresh`, `stale`, `missing`, `unknown`, and `invalid`. Only `fresh` proves that coverage metadata matches the current HEAD; every other status remains a warning with the update command recorded in the artifact.
- On hosts without a detectable Docker or Podman engine, non-CI coverage runs can fail in `tests/container/container-agent.test.ts`. Use `CI=1 pnpm run coverage` when the intent is to emulate CI degraded-mode behavior locally, and record that condition with the evidence.

Latest observed `origin/main` baseline for the enforced workflow as of 2026-07-02 on main-push run `28600653332`:

| Metric | Percent | Covered / Total |
| --- | ---: | ---: |
| Lines | 36.18% | not recorded in the workflow log |

### Recommended Operations
- On PRs, use `/coverage <pct>` for ad-hoc threshold overrides.
- On PRs, use `/enforce-coverage` when coverage should become blocking.
- On `main`, configure repository variable `COVERAGE_ENFORCE_MAIN=1`; keep the target at `80%` and advance `configs/coverage-ratchet.json.mainThreshold` until it reaches the target.
- Roll out branch protection in stages: start with the current ratchet threshold, then raise the ratchet after the threshold is stable.

### Step-by-Step: Enable on `main`
1. In Settings -> Variables -> Repository variables, add:
   - `COVERAGE_ENFORCE_MAIN=1`
   - optional `COVERAGE_TARGET_THRESHOLD` such as `80` when the target differs from the checked-in default
2. Confirm that `configs/coverage-ratchet.json.mainThreshold` matches the latest observed `main` baseline and that the `targetThreshold` remains `80`.
3. After the operational baseline is stable, add the relevant `coverage-check` status contexts to branch protection and raise the checked-in ratchet in follow-up PRs.

### Notes
- PR comments are still emitted when the repository variables are unset; this remains report-only behavior.
- Agree on the threshold only after observing real deviation frequency on `main`.
- Coverage policy affects coverage gating only. It does not replace broader `verify-lite`, `policy-gate`, or `gate` requirements.

### Development (Local Verify)
- Dry-run the summary composer locally without posting to GitHub:

```bash
AE_COVERAGE_DRY_RUN=1 \
GITHUB_TOKEN=dummy \
GITHUB_REPOSITORY=owner/repo \
GITHUB_EVENT_NAME=pull_request \
GITHUB_EVENT_PATH=event.json \
node scripts/coverage/pr-coverage-summary.mjs
```

- The script searches for coverage JSON in this order:
  - `coverage/coverage-summary.json`
  - `artifacts/coverage/coverage-summary.json`
- The default project command emits the required JSON summary:

```bash
pnpm run coverage
```

- Override the summary path with `AE_COVERAGE_SUMMARY_PATH` when an alternate file already exists.
- Disable comment posting for CI experiments with `AE_COVERAGE_SKIP_COMMENT=1`.

### FAQ
- Why does a PR fail outside `main`?
  - The default is report-only. Outside `main`, failures usually mean `enforce-coverage` was applied or the workflow logic around threshold derivation was modified.
- How is the threshold chosen?
  - PRs use `coverage:<pct>` label -> repository variable `COVERAGE_DEFAULT_THRESHOLD` -> default `80`. Enforced `main` pushes without a label use `configs/coverage-ratchet.json.mainThreshold` capped by the target threshold.
- How do we make `main` required?
  - Set `COVERAGE_ENFORCE_MAIN=1`, confirm the checked-in ratchet baseline, observe for a period, then add the relevant `coverage-check` status context in branch protection.
- Why is `coverage-summary.json` missing under strict execution?
  - Confirm that `pnpm run coverage` emits the `json-summary` reporter output and that CI preserves the generated `coverage/` content.

### PR Comment Example
```text
<!-- AE-COVERAGE-SUMMARY -->
Coverage (lines): 82%
Threshold (effective): 80%
Gate: OK (82% >= 80%) [non-blocking]
- via label: coverage:80
- repo var: COVERAGE_DEFAULT_THRESHOLD=80%
- default: 80%
Derived: label > repo var > default
Rules: label override last-wins; accepts 0–100; trims %/spaces
Policy: report-only
Policy source: report-only
Docs: docs/quality/coverage-required.md
Docs: docs/quality/coverage-policy.md
Docs: docs/ci/label-gating.md
Tips: /coverage <pct> to override; /enforce-coverage to enforce
Reproduce: coverage → coverage/coverage-summary.json → total.lines.pct
Reproduce: threshold → label coverage:<pct> > vars.COVERAGE_DEFAULT_THRESHOLD > default 80
Source: label
```

On enforced `main` push notes, the workflow additionally prints `Threshold source`, `Ratchet threshold`, and `Target threshold`; its derivation order is `label > main ratchet > repo var > default`.

### Branch Protection
1. Set repository variables:
   - `COVERAGE_ENFORCE_MAIN=1`
   - optional `COVERAGE_TARGET_THRESHOLD` if the target differs from the checked-in default
2. Maintain `configs/coverage-ratchet.json.mainThreshold` through reviewable PRs until it reaches `80`.
3. In Settings -> Branches -> Branch protection rules -> `main` -> Require status checks, add the relevant `coverage-check` contexts such as `coverage-check / gate` or `coverage-check / coverage`.
4. Keep an observation period before raising the ratchet further.

### References
- Workflow: `.github/workflows/coverage-check.yml`
- Slash commands: repository-root AGENTS.md, `docs/ci-policy.md`
- Related docs:
  - `docs/quality/coverage-required.md`
  - `docs/quality/verification-gates.md`
  - `docs/ci/label-gating.md`

## 日本語

### 目的
- PR 処理は既定で高速かつ報告専用（report-only）に保つ
- オペレーターまたはブランチポリシーが明示した場合のみ coverage をブロッキングに引き上げる
- `main` では段階的 ratchet によって threshold を統制し、最終目標 `80%` までレビュー可能な単位で引き上げる

### 仕組み

しきい値の決定順序:
1. PR ラベル `coverage:<pct>`（例: `coverage:75`）
2. 明示的な緊急 override が必要な場合は、リポジトリ変数 `COVERAGE_RATCHET_THRESHOLD`
3. 強制モードの `main` push では、`configs/coverage-ratchet.json.mainThreshold` を target threshold で上限設定した値
4. リポジトリ変数 `COVERAGE_DEFAULT_THRESHOLD`（既定値 `80`）

ラベルの解釈規則:
- `.github/workflows/coverage-check.yml` では、小文字の `coverage:` で始まる最初のラベルを採用する
- `coverage:` の後ろの値は JavaScript の `Number(...)` にそのまま渡される
- gate workflow 側では追加の trim、case-folding、range validation は行わない
- `scripts/coverage/pr-coverage-summary.mjs` は comment 表示のためにより積極的な正規化を行うため、差分がある場合は gate 側の挙動を正とする

ブロッキング強制は次のいずれかで有効になります。
- PR に `enforce-coverage` ラベルが付いている
- `main` への push で workflow が実行され、かつ `COVERAGE_ENFORCE_MAIN=1` が設定されている
- `coverage-check` を `workflow_dispatch` で手動起動し、input `strict=true` を指定した手動 override を使う

報告時の挙動:
- `.github/workflows/coverage-check.yml` は非ブロッキングの PR コメントを投稿し、effective coverage、effective threshold、threshold source、現在の policy state を記録する
- Verify Lite のログは現在の `COVERAGE_ENFORCE_MAIN` 設定と設定済み既定しきい値を記録するが、effective threshold 自体は計算・出力しない

### 80% へ向けた main ratchet
- 長期目標は line coverage `80%` のまま維持します。
- `configs/coverage-ratchet.json` は、現在 `main` で強制可能な threshold と、その根拠となる観測 evidence を記録します。
- 2026-07-02 の run `28600653332` では `main` の line coverage が `36.18%` だったため、初期 ratchet threshold は `36.18%` です。
- `main` が現行 threshold で安定して green になった後、`configs/coverage-ratchet.json.mainThreshold` を小さな増分で引き上げます。`minimumStep` は推奨する最小引き上げ幅を表します。
- ratchet threshold を下げる場合は、明示的な incident rollback として理由、証跡、後続 owner を残してください。

### Baseline freshness と generated artifact
- `pnpm run coverage` は local coverage evidence を生成する project の標準コマンドです。
- このコマンドは `coverage/coverage-summary.json` と `coverage/lcov.info` を出力します。`coverage/` は `.gitignore` で除外されており、手動管理する tracked baseline ではなく generated evidence として扱います。
- baseline を文書に記録する場合は、対象 commit、command、date、関連する environment flag を併記します。古い local `coverage/` directory だけから鮮度を判断しないでください。
- `pnpm run coverage:freshness` は `coverage/coverage-summary.json` を読み、report-only freshness evidence を `artifacts/testing/coverage-freshness.json` と `artifacts/testing/coverage-freshness.md` に出力します。
- freshness status は `fresh`、`stale`、`missing`、`unknown`、`invalid` です。coverage metadata が current HEAD と一致することを証明できるのは `fresh` のみで、それ以外は artifact に更新コマンドを記録した warning として扱います。
- Docker / Podman engine を検出できない host では、non-CI の coverage run が `tests/container/container-agent.test.ts` で失敗する場合があります。CI degraded-mode を local で再現したい場合は `CI=1 pnpm run coverage` を使い、その条件を evidence として記録します。

2026-07-02 時点の main-push run `28600653332` で確認した latest observed baseline:

| Metric | Percent | Covered / Total |
| --- | ---: | ---: |
| Lines | 36.18% | workflow log には未記録 |

### 推奨運用
- PR では `/coverage <pct>` で一時的なしきい値 override を行う
- PR では `/enforce-coverage` で coverage をブロッキングに切り替える
- `main` では `COVERAGE_ENFORCE_MAIN=1` を設定し、target `80%` を維持したまま `configs/coverage-ratchet.json.mainThreshold` を段階的に引き上げる
- branch protection は段階導入とし、まずは現行 ratchet threshold で安定化させ、その後 ratchet を引き上げる

### `main` で有効化する手順
1. Settings -> Variables -> Repository variables に次を追加する
   - `COVERAGE_ENFORCE_MAIN=1`
   - target を checked-in default から変える場合のみ `COVERAGE_TARGET_THRESHOLD`（例: `80`）
2. `configs/coverage-ratchet.json.mainThreshold` が最新の `main` baseline と整合し、`targetThreshold` が `80` のままであることを確認する
3. 運用 baseline が安定したら、branch protection に関連する `coverage-check` status context を追加し、後続 PR で ratchet を引き上げる

### 注意事項
- リポジトリ変数が未設定でも PR コメントは出力される。これは報告専用（report-only）挙動である
- threshold は `main` での逸脱頻度を実測したうえで合意する
- coverage policy は coverage gate だけを制御する。`verify-lite`、`policy-gate`、`gate` 全体の代替ではない

### Development（ローカル検証）
- GitHub 投稿なしで summary 生成処理を dry-run する:

```bash
AE_COVERAGE_DRY_RUN=1 \
GITHUB_TOKEN=dummy \
GITHUB_REPOSITORY=owner/repo \
GITHUB_EVENT_NAME=pull_request \
GITHUB_EVENT_PATH=event.json \
node scripts/coverage/pr-coverage-summary.mjs
```

- script は coverage JSON を次の順で探索する
  - `coverage/coverage-summary.json`
  - `artifacts/coverage/coverage-summary.json`
- 既定の project command は必要な JSON summary を出力する:

```bash
pnpm run coverage
```

- 別の summary ファイルを使う場合は、既存ファイルを `AE_COVERAGE_SUMMARY_PATH` で明示する
- CI 実験で comment 投稿を止める場合は `AE_COVERAGE_SKIP_COMMENT=1` を使う

### FAQ
- `main` 以外の PR で失敗になるのはなぜか
  - 既定は report-only。`enforce-coverage` が付いたか、threshold 導出ロジックが変更された可能性を確認する
- しきい値はどう決まるか
  - PR では `coverage:<pct>` label -> repository variable `COVERAGE_DEFAULT_THRESHOLD` -> 既定 `80`。ラベルのない強制 `main` push では `configs/coverage-ratchet.json.mainThreshold` を target threshold で上限設定した値を使う
- `main` を required にするにはどうするか
  - `COVERAGE_ENFORCE_MAIN=1` を設定し、checked-in ratchet baseline を確認し、一定期間観測した後にブランチ保護へ追加する
- strict 実行で `coverage-summary.json` が missing になるのはなぜか
  - `pnpm run coverage` が `json-summary` reporter を出力しているか、および CI が `coverage/` の生成物を保持しているかを確認する

### PR comment 例
```text
<!-- AE-COVERAGE-SUMMARY -->
Coverage (lines): 82%
Threshold (effective): 80%
Gate: OK (82% >= 80%) [non-blocking]
- via label: coverage:80
- repo var: COVERAGE_DEFAULT_THRESHOLD=80%
- default: 80%
Derived: label > repo var > default
Rules: label override last-wins; accepts 0–100; trims %/spaces
Policy: report-only
Policy source: report-only
Docs: docs/quality/coverage-required.md
Docs: docs/quality/coverage-policy.md
Docs: docs/ci/label-gating.md
Tips: /coverage <pct> to override; /enforce-coverage to enforce
Reproduce: coverage → coverage/coverage-summary.json → total.lines.pct
Reproduce: threshold → label coverage:<pct> > vars.COVERAGE_DEFAULT_THRESHOLD > default 80
Source: label
```

強制モードの `main` push note では、workflow が `Threshold source`、`Ratchet threshold`、`Target threshold` も出力します。この場合の導出順は `label > main ratchet > repo var > default` です。

### Branch protection
1. リポジトリ変数を設定する
   - `COVERAGE_ENFORCE_MAIN=1`
   - target を checked-in default から変える場合のみ `COVERAGE_TARGET_THRESHOLD`
2. `configs/coverage-ratchet.json.mainThreshold` を reviewable PR で管理し、`80` に到達するまで段階的に引き上げる
3. Settings -> Branches -> Branch protection rules -> `main` -> Require status checks で、`coverage-check / gate` や `coverage-check / coverage` など必要な context を追加する
4. ratchet をさらに引き上げる前に、一定期間は観測期間を設ける

### 参照
- Workflow: `.github/workflows/coverage-check.yml`
- Slash commands: repository root の AGENTS.md, `docs/ci-policy.md`
- 関連文書:
  - `docs/quality/coverage-required.md`
  - `docs/quality/verification-gates.md`
  - `docs/ci/label-gating.md`
