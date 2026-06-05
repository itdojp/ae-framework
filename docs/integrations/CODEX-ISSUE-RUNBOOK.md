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

Record the source URL in the task file so later PRs can show which Issue was used.

### 2. Non-interactive Codex execution

Use non-interactive execution when the task is well bounded and the repository can be modified inside the declared workspace. Keep the working directory inside the repository or an isolated worktree.

```bash
codex exec \
  --cd "$WORK" \
  --sandbox workspace-write \
  --ask-for-approval never \
  - < "$WORK/.codex-local/tasks/issue-$ISSUE.md"
```

Do not use this command for unbounded multi-Issue writes in a shared worktree. Use one worktree per Issue when parallelizing.

### 3. Interactive Codex execution

Use interactive mode when the Issue needs interpretation, review, or stepwise confirmation.

```bash
codex --cd "$WORK"
```

Then paste the Issue title, URL, body, acceptance criteria, and any explicit validation commands. Keep the original scope intact.

### 4. Pre-work checklist

Before changing files:

1. Read `AGENTS.md`.
2. Read the Issue body and identify target files, acceptance criteria, and validation commands.
3. Read target files and nearby README / runbook / schema files.
4. Check the working tree:

   ```bash
   git status --short
   git branch --show-current
   ```

5. If a clean workspace is needed, create a dedicated worktree under the current workspace root, for example:

   ```bash
   git fetch origin main --prune
   git worktree add ../ae-framework-issue-$ISSUE -b work/issue-$ISSUE origin/main
   ```

### 5. Post-work checklist

Before opening or updating a PR:

```bash
git diff --stat
git diff --check
```

Run the Issue-specific validation commands. At minimum for docs/contracts work:

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
```

If commands cannot be run, write the command and the concrete reason in the PR body. If generated artifacts are expected, inspect their paths and include them in the PR summary.

### 6. PR and review checklist

1. Include `Closes #<issue>` in the PR body.
2. Include Summary, Acceptance, Verification, and Rollback sections.
3. Request GitHub Copilot review when repository policy requires it.
4. Inspect review bodies and inline comments.
5. Reply to each actionable comment and resolve each review thread.
6. Use review-completeness checking before declaring review done.
7. Wait for required checks (`verify-lite`, `policy-gate`, and `gate`) and inspect full check board for non-pass entries.

### 7. Subagent / parallel task safety boundary

- Main agent owns writes, commits, pushes, PR creation, and Issue updates.
- Subagents are read-only investigation helpers unless the human explicitly approves otherwise.
- Parallel Issue work must use separate worktrees, for example `../ae-framework-3434-*` and `../ae-framework-3435-*`.
- Never let two agents write the same file set without an integration owner.
- After any delegated investigation, inspect `git status --short`, `git diff --stat`, and the final response before adopting findings.
- Producer output from a subagent is not trusted evidence until the main agent validates it against repository files and commands.

### 8. Evidence expected in the PR body

```text
## Verification
- pnpm -s run check:doc-consistency
- pnpm -s run check:schemas
- <issue-specific command>

## Notes
- Not run: <command> — <reason>
- Generated artifacts inspected: <path>
```

---

## 日本語

GitHub Issue を Codex CLI の作業入力にする場合は、この runbook を使います。Issue 本文は producer input です。権威ある control-plane evidence は、repository state、`AGENTS.md`、target files、validation commands、PR reviews、CI checks です。

### 1. Issue を task file に変換する

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

後続 PR で参照元を示せるよう、task file には Issue URL を残します。

### 2. 非対話実行

作業範囲が明確で、declared workspace 内で編集できる場合は非対話実行を使います。working directory は repository または隔離 worktree の中に置きます。

```bash
codex exec \
  --cd "$WORK" \
  --sandbox workspace-write \
  --ask-for-approval never \
  - < "$WORK/.codex-local/tasks/issue-$ISSUE.md"
```

共有 worktree で複数 Issue をまとめて書き換える用途には使いません。並行処理する場合は Issue ごとに worktree を分けます。

### 3. 対話実行

Issue の解釈や段階的な確認が必要な場合は interactive mode を使います。

```bash
codex --cd "$WORK"
```

起動後、Issue title、URL、body、acceptance criteria、明示された validation commands を貼り付けます。元の scope を狭めないでください。

### 4. 作業前 checklist

編集前に次を確認します。

1. `AGENTS.md` を読む。
2. Issue body から target files、acceptance criteria、validation commands を抽出する。
3. target files と近接する README / runbook / schema を読む。
4. working tree を確認する。

   ```bash
   git status --short
   git branch --show-current
   ```

5. clean workspace が必要な場合は、現在の workspace root 配下に専用 worktree を作る。

   ```bash
   git fetch origin main --prune
   git worktree add ../ae-framework-issue-$ISSUE -b work/issue-$ISSUE origin/main
   ```

### 5. 作業後 checklist

PR 作成または更新前に次を確認します。

```bash
git diff --stat
git diff --check
```

Issue 固有の validation command を実行します。docs/contracts work の最低限は次です。

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
```

実行できない command がある場合は、command と具体的な理由を PR body に残します。生成 artifact が期待される場合は、path を確認して PR summary に含めます。

### 6. PR / review checklist

1. PR body に `Closes #<issue>` を入れる。
2. Summary、Acceptance、Verification、Rollback を書く。
3. repository policy が要求する場合は GitHub Copilot review を依頼する。
4. review body と inline comment を確認する。
5. actionable comment へ返信し、review thread を解決する。
6. review 完了宣言前に review completeness を確認する。
7. required checks（`verify-lite`, `policy-gate`, `gate`）と full check board を確認する。

### 7. subagent / parallel task の安全境界

- 書き込み、commit、push、PR作成、Issue更新は main agent が行います。
- subagent は、人間が明示承認しない限り read-only investigation helper として扱います。
- 複数 Issue を並行処理する場合は `../ae-framework-3434-*` / `../ae-framework-3435-*` のように worktree を分けます。
- integration owner なしに複数 agent が同じ file set を書き換えないようにします。
- delegated investigation 後は `git status --short`、`git diff --stat`、final response を確認してから採用します。
- subagent output は、main agent が repository files と commands で検証するまで信頼済み evidence ではありません。

### 8. PR body に残す evidence

```text
## Verification
- pnpm -s run check:doc-consistency
- pnpm -s run check:schemas
- <issue-specific command>

## Notes
- Not run: <command> — <reason>
- Generated artifacts inspected: <path>
```
