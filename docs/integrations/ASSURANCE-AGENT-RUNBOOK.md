---
docRole: ssot
lastVerified: '2026-05-08'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Assurance Agent Runbook

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This runbook defines how Codex CLI, Claude Code, MCP clients, and similar producer agents should use ae-framework without turning ae-framework into another coding-agent harness.

The operating model is:

```text
Issue / operator intent
  -> producer agent drafts or edits code, specs, tests, and docs
  -> ae-framework validates contracts, generates evidence, evaluates policy, and builds PR/release summaries
  -> human or automation reviews the evidence package before accepting the change
```

ae-framework is the assurance control plane. Producer agents are replaceable. The control plane owns judgment-side contracts, evidence, policy, and PR/release assurance.

### 2. Role split

| Layer | Owns | Examples | Not responsible for |
| --- | --- | --- | --- |
| Producer agent | proposing or editing repo content | Codex CLI, Claude Code, Copilot, Cursor, MCP clients | final assurance judgment |
| Tool producer | generating raw validation output | Vitest, formal tools, conformance checks, security review producers | PR/release acceptability |
| ae-framework control plane | evidence contracts, validation, policy decisions, summaries | `verify:lite`, claim-level summary, policy-gate, change-package v2 | replacing the coding agent |
| Human / merge automation | accepting residual risk and merging | PR reviewer, maintainer, auto-merge policy | inventing missing evidence |

Use the policy document as the canonical decision record: `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md`.

### 3. Issue-driven execution flow

Use this flow for Codex CLI, Claude Code, or another producer agent.

1. Read the issue and parent roadmap.
2. Inspect current HEAD before trusting the issue text:
   - `git status --short`
   - `git log --oneline -n 20`
   - `cat package.json`
3. Identify the affected control-plane areas:
   - docs / policy / design
   - schema / fixtures / contract validation
   - producer scripts
   - CI / policy gates
   - PR summary / change package
4. Implement the smallest coherent slice.
5. Run the narrowest relevant checks, then broader checks when cost-effective.
6. Generate or update evidence artifacts where the slice changes assurance behavior.
7. Open a PR that links the issue and lists evidence.
8. Request AI review when required by the project workflow.
9. Reply to and resolve every actionable review thread.
10. Merge only after required checks are green and the PR summary / change package state is reviewable.

### 4. No-MCP fallback path

MCP is optional. A producer agent can use shell commands directly from the repository root.

Baseline setup:

```bash
corepack enable || true
pnpm install --frozen-lockfile
```

Common validation commands:

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
pnpm -s run verify:lite
```

Assurance evidence commands:

```bash
pnpm -s run verify:assurance
pnpm -s run claim-level-summary:generate
pnpm -s run change-package:generate:dual
pnpm -s run change-package:validate:dual
```

Optional focused end-to-end smoke:

```bash
pnpm -s run assurance:e2e -- --scenario inventory-waiver --output-dir artifacts/assurance-e2e/inventory-waiver/latest
```

Recommended PR evidence package:

- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/assurance/assurance-summary.json`
- `artifacts/assurance/claim-evidence-manifest.json`
- `artifacts/assurance/claim-level-summary.json`
- `artifacts/ci/policy-decision-js-v1.json`
- `artifacts/change-package/change-package-v2.json`
- `artifacts/change-package/change-package-v2.md`

Not every slice produces every artifact. Missing artifacts must be explicit in the summary and must not be described as proof.

### 5. MCP path

Use MCP when the producer environment can call stdio MCP servers. The current repository exposes these script entrypoints:

```bash
pnpm run codex:mcp:intent
pnpm run codex:mcp:test
pnpm run codex:mcp:verify
pnpm run codex:mcp:code
pnpm run codex:mcp:spec
```

Recommended mapping:

| Producer need | MCP server | Script | Expected control-plane follow-up |
| --- | --- | --- | --- |
| Draft or normalize intent | Intent | `pnpm run codex:mcp:intent` | validate resulting requirements / context pack |
| Generate tests | Test generation | `pnpm run codex:mcp:test` | run focused tests and update evidence refs |
| Verify a change | Verify | `pnpm run codex:mcp:verify` | feed summaries into claim-level summary / policy-gate |
| Generate code from structured input | Code generation | `pnpm run codex:mcp:code` | run schema, tests, and change-package validation |
| Compile or validate AE-Spec | Spec synthesis | `pnpm run codex:mcp:spec` | compile, validate, and attach generated artifacts |

When MCP is unavailable, use the no-MCP fallback path. Do not make MCP a prerequisite for `verify:lite`, schema checks, or change-package validation.

### 6. Claude Code hooks / skills guidance

Claude Code hooks and skills are integration aids, not mandatory runtime requirements.

Recommended hook feedback artifact:

```bash
pnpm run hook-feedback:build -- \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --change-package artifacts/change-package/change-package-v2.json
```

Use `docs/agents/hook-feedback.md` for the detailed hook contract. The hook should pass compact evidence and blocking reasons back to the producer agent. It should not hide missing evidence or convert a waived / runtime-mitigated / unresolved claim into a satisfied claim.

Claude-specific documents remain integration references:

- `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`
- `docs/integrations/CLAUDECODE-WORKFLOW.md`
- `docs/agents/hook-feedback.md`

Codex-specific documents remain integration references:

- `docs/integrations/CODEX-INTEGRATION.md`
- `docs/integrations/CODEX-CONTINUATION-CONTRACT.md`
- `docs/integrations/CODEX-VENDOR-NEUTRAL-BOUNDARY.md`
- `docs/integrations/CODEX-SECURITY-AUDIT.md`

### 7. Expected PR summary content

For an assurance-relevant PR, the PR body or generated comment should include:

- linked issue and scope;
- files and contracts changed;
- validation commands and results;
- generated evidence package path;
- claim-state counts or reason they are not applicable;
- policy decision and enforcement mode;
- waiver / runtime-control / unresolved / failed / not-applicable status when present;
- residual risks and post-deploy controls;
- review completeness and CI status before merge.

Use `change-package/v2` when the slice changes assurance contracts or PR/release judgment behavior.

### 8. Minimal smoke path

For a docs-only integration update:

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
```

For a producer / MCP / hook change:

```bash
pnpm -s run test:agents:smoke
pnpm -s run verify:lite
```

For a proof-carrying assurance change:

```bash
pnpm -s run claim-level-summary:generate
pnpm -s run change-package:generate:dual
pnpm -s run change-package:validate:dual
pnpm -s run assurance:e2e -- --scenario inventory-waiver --output-dir artifacts/assurance-e2e/inventory-waiver/latest
```

If an environment dependency is unavailable, record the exact reason and the closest passing focused validation. Do not claim the missing lane passed.

### 9. What ae-framework does not do

- It does not replace Codex CLI, Claude Code, Copilot, Cursor, or another coding agent.
- It does not guarantee high assurance from a green build alone.
- It does not require formal proof for every change.
- It does not make MCP mandatory for local or CI validation.
- It does not convert human waivers or runtime mitigations into proof.

---

## 日本語

## 1. 目的

この runbook は、Codex CLI、Claude Code、MCP client、および類似の producer agent が、ae-framework を coding-agent harness としてではなく assurance control plane として使う標準手順を定義します。

運用モデルは次の通りです。

```text
Issue / operator intent
  -> producer agent が code / spec / test / docs を作成・編集
  -> ae-framework が contract validation、evidence 生成、policy 評価、PR/release summary を実行
  -> human または merge automation が evidence package を確認して受け入れ判断
```

ae-framework は assurance control plane です。producer agent は交換可能です。control plane は判断側の contract、evidence、policy、PR/release assurance を扱います。

## 2. 役割分担

| レイヤ | 責務 | 例 | 責務外 |
| --- | --- | --- | --- |
| Producer agent | repo 内容の提案・編集 | Codex CLI、Claude Code、Copilot、Cursor、MCP client | 最終 assurance 判断 |
| Tool producer | raw validation output の生成 | Vitest、formal tools、conformance checks、security review producer | PR/release の受入判断 |
| ae-framework control plane | evidence contract、validation、policy decision、summary | `verify:lite`、claim-level summary、policy-gate、change-package v2 | coding agent の代替 |
| Human / merge automation | residual risk の受入と merge | PR reviewer、maintainer、auto-merge policy | missing evidence の捏造 |

canonical policy は `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` を参照します。

## 3. Issue-driven execution flow

Codex CLI、Claude Code、その他 producer agent では次の流れを使います。

1. issue と親 roadmap を読む。
2. issue 本文を事実として扱う前に current HEAD を確認する。
   - `git status --short`
   - `git log --oneline -n 20`
   - `cat package.json`
3. 影響する control-plane 領域を特定する。
   - docs / policy / design
   - schema / fixtures / contract validation
   - producer scripts
   - CI / policy gates
   - PR summary / change package
4. 最小の一貫した slice を実装する。
5. まず狭い検証を実行し、必要に応じて広い検証を実行する。
6. assurance behavior を変える場合は evidence artifact を生成・更新する。
7. issue に紐づく PR を作成し、evidence を記載する。
8. プロジェクト運用上必要な場合は AI review を依頼する。
9. actionable review thread は全件返信・解決する。
10. required check が green で、PR summary / change package が reviewable になってから merge する。

## 4. MCP なしの fallback path

MCP は任意です。producer agent は repository root から shell command を直接実行できます。

基本セットアップ:

```bash
corepack enable || true
pnpm install --frozen-lockfile
```

通常検証:

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
pnpm -s run verify:lite
```

assurance evidence:

```bash
pnpm -s run verify:assurance
pnpm -s run claim-level-summary:generate
pnpm -s run change-package:generate:dual
pnpm -s run change-package:validate:dual
```

任意の focused end-to-end smoke:

```bash
pnpm -s run assurance:e2e -- --scenario inventory-waiver --output-dir artifacts/assurance-e2e/inventory-waiver/latest
```

推奨 PR evidence package:

- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/assurance/assurance-summary.json`
- `artifacts/assurance/claim-evidence-manifest.json`
- `artifacts/assurance/claim-level-summary.json`
- `artifacts/ci/policy-decision-js-v1.json`
- `artifacts/change-package/change-package-v2.json`
- `artifacts/change-package/change-package-v2.md`

すべての slice がすべての artifact を生成するわけではありません。missing artifact は明示し、proof として扱いません。

## 5. MCP path

producer 環境が stdio MCP server を呼び出せる場合に使います。現行 repository の entrypoint は次です。

```bash
pnpm run codex:mcp:intent
pnpm run codex:mcp:test
pnpm run codex:mcp:verify
pnpm run codex:mcp:code
pnpm run codex:mcp:spec
```

| Producer need | MCP server | Script | control-plane follow-up |
| --- | --- | --- | --- |
| intent の作成・正規化 | Intent | `pnpm run codex:mcp:intent` | requirements / context pack を検証 |
| test 生成 | Test generation | `pnpm run codex:mcp:test` | focused tests 実行と evidence refs 更新 |
| 変更検証 | Verify | `pnpm run codex:mcp:verify` | summary を claim-level summary / policy-gate に接続 |
| 構造化入力から code 生成 | Code generation | `pnpm run codex:mcp:code` | schema / tests / change-package validation を実行 |
| AE-Spec compile / validate | Spec synthesis | `pnpm run codex:mcp:spec` | compile / validate / artifact 添付 |

MCP が使えない場合は no-MCP fallback path を使います。`verify:lite`、schema check、change-package validation に MCP を必須化しません。

## 6. Claude Code hooks / skills guidance

Claude Code hooks / skills は統合補助であり、必須 runtime ではありません。

推奨 hook feedback artifact:

```bash
pnpm run hook-feedback:build -- \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --assurance-summary artifacts/assurance/assurance-summary.json \
  --change-package artifacts/change-package/change-package-v2.json
```

詳細 contract は `docs/agents/hook-feedback.md` を参照します。hook は compact evidence と blocking reason を producer agent に戻します。missing evidence を隠したり、waived / runtime-mitigated / unresolved claim を satisfied claim に変換してはいけません。

Claude 関連の参照:

- `docs/integrations/CLAUDE-CODE-TASK-TOOL-INTEGRATION.md`
- `docs/integrations/CLAUDECODE-WORKFLOW.md`
- `docs/agents/hook-feedback.md`

Codex 関連の参照:

- `docs/integrations/CODEX-INTEGRATION.md`
- `docs/integrations/CODEX-CONTINUATION-CONTRACT.md`
- `docs/integrations/CODEX-VENDOR-NEUTRAL-BOUNDARY.md`
- `docs/integrations/CODEX-SECURITY-AUDIT.md`

## 7. PR summary に含める内容

assurance に関係する PR では、PR body または生成コメントに次を含めます。

- linked issue と scope;
- 変更した files / contracts;
- validation commands と結果;
- generated evidence package path;
- claim-state counts または applicable でない理由;
- policy decision と enforcement mode;
- waiver / runtime-control / unresolved / failed / not-applicable がある場合の状態;
- residual risks と post-deploy controls;
- merge 前の review completeness と CI status。

assurance contract または PR/release judgment behavior を変える slice では `change-package/v2` を使います。

## 8. Minimal smoke path

docs-only integration update:

```bash
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
```

producer / MCP / hook change:

```bash
pnpm -s run test:agents:smoke
pnpm -s run verify:lite
```

proof-carrying assurance change:

```bash
pnpm -s run claim-level-summary:generate
pnpm -s run change-package:generate:dual
pnpm -s run change-package:validate:dual
pnpm -s run assurance:e2e -- --scenario inventory-waiver --output-dir artifacts/assurance-e2e/inventory-waiver/latest
```

環境依存が満たせない場合は、理由と最も近い focused validation を記録します。未実行の lane を pass と表現しません。

## 9. ae-framework がしないこと

- Codex CLI、Claude Code、Copilot、Cursor など coding agent の代替にならない。
- green build だけで high assurance を保証しない。
- 全変更に formal proof を要求しない。
- local / CI validation に MCP を必須化しない。
- human waiver や runtime mitigation を proof に変換しない。
