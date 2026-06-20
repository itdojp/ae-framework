---
docRole: derived
canonicalSource:
- AGENTS.md
- docs/agents/agent-producer-matrix.md
- docs/integrations/CODEX-INTEGRATION.md
lastVerified: '2026-06-05'
---

# Codex CLI GitHub Issue Runbook

> Language / 言語: English | 日本語

---

## English

Use this runbook when a GitHub Issue is the work input for Codex CLI. The Issue body is producer input. The repository state, `AGENTS.md`, target files, validation commands, PR reviews, and CI checks remain the authoritative control-plane evidence.

### 1. Convert an Issue into a task file

Recommended helper:

```bash
REPO=itdojp/ae-framework
ISSUE=3434
WORK=/path/to/ae-framework

node scripts/codex/export-issue-task.mjs \
  --repo "$REPO" \
  --issue "$ISSUE" \
  --work "$WORK" \
  --print-commands
```

The helper writes `.codex-local/tasks/issue-$ISSUE.md`, preserves the Issue URL,
adds the Context Pack preflight block, and prints dedicated worktree / `codex
exec` examples with a preflight reminder. It refuses output paths outside
`--work`, including existing symlinked output directories that resolve outside
the worktree.

Manual bash equivalent:

```bash
REPO=itdojp/ae-framework
ISSUE=3434
WORK=/path/to/ae-framework

mkdir -p "$WORK/.codex-local/tasks"
gh issue view "$ISSUE" --repo "$REPO" \
  --json title,body,url \
  --jq '"# " + .title + "\n\nIssue: " + .url + "\n\n" + .body' \
  > "$WORK/.codex-local/tasks/issue-$ISSUE.md"
```

PowerShell equivalent:

```powershell
$Repo = "itdojp/ae-framework"
$Issue = 3434
$Work = "C:/path/to/ae-framework"

pwsh -NoProfile -File scripts/codex/Export-CodexIssueTask.ps1 `
  -Repo $Repo `
  -Issue $Issue `
  -Work $Work `
  -PrintCommands
```

If the helper is unavailable, use `gh issue view ... --json title,body,url |
ConvertFrom-Json` and write the same `# <title>`, `Issue: <url>`, metadata,
Context Pack preflight, and Issue body fields to `.codex-local/tasks/issue-N.md`.

The task file is local operator input. `.gitignore` excludes `.codex-local/tasks/`, and agents must not stage task files. Record the source URL in the task file so later PRs can show which Issue was used without copying the full local file into the commit.

### 2. Context Pack preflight block for the task file

Add or preserve this block near the top of the local task file before running Codex. It mirrors `AGENTS.md` routing and treats Context Pack as design SSOT, not as an optional prompt.

```markdown
## Context Pack preflight

- Read `AGENTS.md`.
- Read `docs/spec/context-pack.md` and `spec/context-pack/boundary-map.json`.
- Identify the Context Pack `objects`, `morphisms`, `diagrams`, `acceptance_tests`, and existing tests relevant to the Issue target files.
- If the requested change conflicts with Context Pack constraints or the boundary map, stop before implementation and record `Context Pack conflict: found` with the conflicting IDs/paths in the PR or Issue comment.
- If no conflict is found, record `Context Pack conflict: none` in the PR body.
- Do not promote routine changes to MBT, property, or formal lanes unless the Issue, risk label, assurance profile, or critical-core boundary requires it.
```

Preflight is a read/stop rule. It does not create a new heavy verification requirement for ordinary changes.

### 3. Non-interactive Codex execution

Use non-interactive execution when the task is well bounded and the repository can be modified inside the declared workspace. Keep the working directory inside the repository or an isolated worktree.

```bash
codex exec \
  --cd "$WORK" \
  --sandbox workspace-write \
  --ask-for-approval never \
  - < "$WORK/.codex-local/tasks/issue-$ISSUE.md"
```

Do not use this command for unbounded multi-Issue writes in a shared worktree. Use one worktree per Issue when parallelizing.

### 4. Interactive Codex execution

Use interactive mode when the Issue needs interpretation, review, or stepwise confirmation.

```bash
codex --cd "$WORK"
```

Then paste the Issue title, URL, body, acceptance criteria, and any explicit validation commands. Keep the original scope intact.

### 5. Pre-work checklist

Before changing files:

1. Read `AGENTS.md`.
2. Read the Issue body and identify target files, acceptance criteria, and validation commands.
3. Run the Context Pack preflight: read `docs/spec/context-pack.md`, `spec/context-pack/boundary-map.json`, and the relevant `acceptance_tests` / existing tests before editing.
4. If the request conflicts with Context Pack constraints or the boundary map, stop and report `Context Pack conflict: found` instead of silently implementing.
5. Read target files and nearby README / runbook / schema files.
6. Check the working tree:

   ```bash
   git status --short
   git branch --show-current
   ```

7. If a clean workspace is needed, create a dedicated worktree under the current workspace root, for example:

   ```bash
   git fetch origin main --prune
   git worktree add ../ae-framework-$ISSUE-work -b work/issue-$ISSUE origin/main
   ```

   Use one worktree per Issue for parallel work. Do not reuse a shared worktree
   for multiple concurrent Issue implementations.

### 6. Post-work checklist

Before opening or updating a PR:

```bash
git diff --stat
git diff --check
git status --short --untracked-files=all
```

Run the Issue-specific validation commands. At minimum for docs/contracts work:

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
```

If commands cannot be run, write the command and the concrete reason in the PR body. If generated artifacts are expected, inspect their paths and include them in the PR summary. Before staging, remove or keep ignored any local task files under `.codex-local/tasks/`; do not use broad staging until `git status --short --untracked-files=all` confirms that no local task input can be committed.

### 7. PR and review checklist

1. Include `Closes #<issue>` in the PR body.
2. Include Summary, Acceptance, Verification, Rollback, and `Context Pack conflict: none` or `Context Pack conflict: found` sections.
3. Request GitHub Copilot review when repository policy requires it.
4. Inspect review bodies and inline comments.
5. Reply to each actionable comment and resolve each review thread.
6. Use review-completeness checking before declaring review done.
7. Wait for the authoritative required checks (`verify-lite`, `policy-gate`) and inspect `gate` / the full check board for non-pass entries.

### 8. Subagent / parallel task safety boundary

- Main agent owns writes, commits, pushes, PR creation, and Issue updates.
- Subagents are read-only investigation helpers unless the human explicitly approves otherwise.
- Parallel Issue work must use separate worktrees, for example `../ae-framework-$ISSUE-*` for each Issue number.
- Never let two agents write the same file set without an integration owner.
- After any delegated investigation, inspect `git status --short`, `git diff --stat`, and the final response before adopting findings.
- Producer output from a subagent is not trusted evidence until the main agent validates it against repository files and commands.

### 9. Evidence expected in the PR body

```text
## Verification
- pnpm -s run check:doc-consistency
- pnpm -s run check:schemas
- <issue-specific command>

## Context Pack conflict
- none | found: <conflicting Context Pack / boundary map IDs and required decision>

## Notes
- Not run: <command> — <reason>
- Generated artifacts inspected: <path>
```

---

## 日本語

GitHub Issue を Codex CLI の作業入力にする場合は、この runbook を使います。Issue 本文は producer input です。権威ある control-plane evidence は、repository state、`AGENTS.md`、target files、validation commands、PR reviews、CI checks です。

### 1. Issue を task file に変換する

推奨 helper:

```bash
REPO=itdojp/ae-framework
ISSUE=3434
WORK=/path/to/ae-framework

node scripts/codex/export-issue-task.mjs \
  --repo "$REPO" \
  --issue "$ISSUE" \
  --work "$WORK" \
  --print-commands
```

helper は `.codex-local/tasks/issue-$ISSUE.md` を作成し、Issue URL、
Context Pack preflight block、専用 worktree / `codex exec` 例を残します。
出力例には preflight reminder も含まれます。`--work` の外側へ出力する
path は拒否し、既存の symlink 経由で worktree 外に解決される出力先も
拒否します。

手動 bash 手順:

```bash
REPO=itdojp/ae-framework
ISSUE=3434
WORK=/path/to/ae-framework

mkdir -p "$WORK/.codex-local/tasks"
gh issue view "$ISSUE" --repo "$REPO" \
  --json title,body,url \
  --jq '"# " + .title + "\n\nIssue: " + .url + "\n\n" + .body' \
  > "$WORK/.codex-local/tasks/issue-$ISSUE.md"
```

PowerShell での同等手順:

```powershell
$Repo = "itdojp/ae-framework"
$Issue = 3434
$Work = "C:/path/to/ae-framework"

pwsh -NoProfile -File scripts/codex/Export-CodexIssueTask.ps1 `
  -Repo $Repo `
  -Issue $Issue `
  -Work $Work `
  -PrintCommands
```

helper が使えない場合は、`gh issue view ... --json title,body,url |
ConvertFrom-Json` を使い、`# <title>`、`Issue: <url>`、metadata、Context
Pack preflight、Issue body を `.codex-local/tasks/issue-N.md` に書き込みます。

task file は local operator input です。`.gitignore` は `.codex-local/tasks/` を除外し、agent は task file を stage してはいけません。後続 PR で参照元を示せるよう、task file には Issue URL を残しますが、local file 全文を commit に含めないでください。

### 2. task file 用 Context Pack preflight block

Codex 実行前に、local task file の先頭付近へ次の block を追加または維持します。これは `AGENTS.md` の router と整合し、Context Pack を任意 prompt ではなく design SSOT として扱うためのものです。

```markdown
## Context Pack preflight

- `AGENTS.md` を読む。
- `docs/spec/context-pack.md` と `spec/context-pack/boundary-map.json` を読む。
- Issue target files に関係する Context Pack の `objects`、`morphisms`、`diagrams`、`acceptance_tests` と既存テストを特定する。
- 依頼内容が Context Pack constraints または boundary map と矛盾する場合は、実装前に停止し、PR または Issue comment に `Context Pack conflict: found` と矛盾する ID / path を記録する。
- 矛盾がない場合は、PR body に `Context Pack conflict: none` を記録する。
- Issue、risk label、assurance profile、critical-core boundary が要求しない限り、通常変更を MBT / property / formal lane へ昇格しない。
```

Preflight は読む・止めるための規則であり、通常変更に新しい heavy verification を要求するものではありません。

### 3. 非対話実行

作業範囲が明確で、declared workspace 内で編集できる場合は非対話実行を使います。working directory は repository または隔離 worktree の中に置きます。

```bash
codex exec \
  --cd "$WORK" \
  --sandbox workspace-write \
  --ask-for-approval never \
  - < "$WORK/.codex-local/tasks/issue-$ISSUE.md"
```

共有 worktree で複数 Issue をまとめて書き換える用途には使いません。並行処理する場合は Issue ごとに worktree を分けます。

### 4. 対話実行

Issue の解釈や段階的な確認が必要な場合は interactive mode を使います。

```bash
codex --cd "$WORK"
```

起動後、Issue title、URL、body、acceptance criteria、明示された validation commands を貼り付けます。元の scope を狭めないでください。

### 5. 作業前 checklist

編集前に次を確認します。

1. `AGENTS.md` を読む。
2. Issue body から target files、acceptance criteria、validation commands を抽出する。
3. Context Pack preflight として、`docs/spec/context-pack.md`、`spec/context-pack/boundary-map.json`、関連する `acceptance_tests` / 既存テストを編集前に読む。
4. 依頼内容が Context Pack constraints または boundary map と矛盾する場合は、無言で実装せず `Context Pack conflict: found` を報告して停止する。
5. target files と近接する README / runbook / schema を読む。
6. working tree を確認する。

   ```bash
   git status --short
   git branch --show-current
   ```

7. clean workspace が必要な場合は、現在の workspace root 配下に専用 worktree を作る。

   ```bash
   git fetch origin main --prune
   git worktree add ../ae-framework-$ISSUE-work -b work/issue-$ISSUE origin/main
   ```

   parallel work では Issue ごとに worktree を分け、複数 Issue の実装を
   shared worktree で同時に進めないでください。

### 6. 作業後 checklist

PR 作成または更新前に次を確認します。

```bash
git diff --stat
git diff --check
git status --short --untracked-files=all
```

Issue 固有の validation command を実行します。docs/contracts work の最低限は次です。

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
```

実行できない command がある場合は、command と具体的な理由を PR body に残します。生成 artifact が期待される場合は、path を確認して PR summary に含めます。stage 前に `.codex-local/tasks/` 配下の local task file を削除するか ignored のままにし、`git status --short --untracked-files=all` で local task input が commit されないことを確認するまで broad staging は使わないでください。

### 7. PR / review checklist

1. PR body に `Closes #<issue>` を入れる。
2. Summary、Acceptance、Verification、Rollback と `Context Pack conflict: none` または `Context Pack conflict: found` を書く。
3. repository policy が要求する場合は GitHub Copilot review を依頼する。
4. review body と inline comment を確認する。
5. actionable comment へ返信し、review thread を解決する。
6. review 完了宣言前に review completeness を確認する。
7. 権威ある required checks（`verify-lite`, `policy-gate`）を待ち、`gate` / full check board に non-pass entry がないか確認する。

### 8. subagent / parallel task の安全境界

- 書き込み、commit、push、PR作成、Issue更新は main agent が行います。
- subagent は、人間が明示承認しない限り read-only investigation helper として扱います。
- 複数 Issue を並行処理する場合は Issue 番号ごとに `../ae-framework-$ISSUE-*` のような worktree を分けます。
- integration owner なしに複数 agent が同じ file set を書き換えないようにします。
- delegated investigation 後は `git status --short`、`git diff --stat`、final response を確認してから採用します。
- subagent output は、main agent が repository files と commands で検証するまで信頼済み evidence ではありません。

### 9. PR body に残す evidence

```text
## Verification
- pnpm -s run check:doc-consistency
- pnpm -s run check:schemas
- <issue-specific command>

## Context Pack conflict
- none | found: <conflicting Context Pack / boundary map IDs and required decision>

## Notes
- Not run: <command> — <reason>
- Generated artifacts inspected: <path>
```
