---
docRole: derived
canonicalSource:
- docs/guides/byo-agent-assurance-quickstart.md
- docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md
- docs/product/evidence-packs/evidence-003-self-dogfood/README.md
lastVerified: '2026-07-01'
---

# First-run Demo: one command to see the assurance review surface

> Language / 言語: English | 日本語

---

## English

This is the recommended first-run path for a new local checkout. It exists so a
new user does not need to compare the reference flow, `first-run`, demo smoke,
or domain pilot routes before seeing the core ae-framework review surface.

After dependency installation, run exactly one demo command:

```bash
pnpm run demo:agent-assurance
```

### Input, command, output, review surface

| Step | Value |
| --- | --- |
| Expected input | Repository fixture data only; no live PR, GitHub token, hosted LLM API, or external agent service is required after dependencies are installed. |
| First command | `pnpm run demo:agent-assurance` |
| Optional artifact check | `pnpm run demo:agent-assurance:check` |
| Main output root | `artifacts/` |
| Reviewer surface to open first | `artifacts/review/agent-assurance-demo/assurance-review.md` |
| Supporting outputs | `artifacts/agents/agent-assurance-demo/producer-normalization-summary.{json,md}`, `artifacts/assurance/agent-assurance-demo/assurance-summary.{json,md}`, `artifacts/policy/agent-assurance-demo/policy-gate-summary.{json,md}`, and `artifacts/verify-lite/agent-assurance-demo/verify-lite-run-summary.json` |
| Evidence proof point | `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md` and `docs/product/evidence-packs/evidence-003-self-dogfood/README.md` show the observed repository dogfooding path behind the demo positioning. |

Open the reviewer Markdown before raw logs. It shows how producer output is
normalized into report-only findings, claim/evidence status, policy summary,
and reviewer actions. It is not approval, merge authority, a live external pilot,
or evidence of generalized review speed, safety, quality, adoption impact, or
agent/vendor superiority.

### Minimal setup

Use the repository package manager first, then run the one command above:

```bash
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install --frozen-lockfile
pnpm run demo:agent-assurance
```

`pnpm run first-run` remains useful as an environment/build/verify baseline, but
it is no longer the first product-evidence demo a new evaluator has to compare
against `demo:agent-assurance`.

The checker is optional and report-only. It verifies the expected
agent-assurance first-run artifact paths after the demo has run; it does not call
GitHub, hosted LLM APIs, or external agent services, and it is not a merge gate.
Run it only after the demo has produced artifacts:

```bash
pnpm run demo:agent-assurance:check
```

### What to read next

1. `docs/guides/byo-agent-assurance-quickstart.md` for the full 15-minute walkthrough.
2. `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md` for the Evidence Sprint case study.
3. `docs/product/evidence-packs/evidence-003-self-dogfood/README.md` for stable evidence links.
4. `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` and `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md` for optional domain-preset pilots.
5. `docs/getting-started/REFERENCE-FLOW.md` when you are ready to map a real Issue-to-PR assurance path.

Advanced flows remain optional and risk/profile-driven: domain presets, formal
lanes, PR posting helpers, and high-assurance strict lanes are not required for
this first demo.

### Troubleshooting

| Symptom | Check | Disposition |
| --- | --- | --- |
| `npm install` fails or is blocked | This repository intentionally uses pnpm workspaces. | Run `corepack enable`, `corepack prepare pnpm@10.0.0 --activate`, then `pnpm install --frozen-lockfile`. |
| `pnpm: command not found` | Corepack may not be enabled for the active Node.js installation. | Use Node.js 20.11+ and run the Corepack commands above. |
| `artifacts/review/agent-assurance-demo/assurance-review.md` is missing | The demo did not complete or artifacts were cleaned. | Re-run `pnpm run demo:agent-assurance`, then run `pnpm run demo:agent-assurance:check` to verify the first-run artifact set. |
| You want to post the review surface to a PR | Posting is not part of the first-run demo. | Follow `docs/guides/byo-agent-assurance-quickstart.md` and keep the posting helper in dry-run mode until `gh auth status` and repository/PR scope are confirmed. |

---

## 日本語

このページは、新規 checkout 後に最初に実行する推奨 demo path です。Reference
flow、`first-run`、demo smoke、domain pilot を比較しなくても、ae-framework の
中心的な review surface を確認できるようにしています。

依存関係を入れた後、最初に実行する command は次の 1 つです。

```bash
pnpm run demo:agent-assurance
```

### 入力・command・出力・review surface

| 項目 | 値 |
| --- | --- |
| 期待入力 | repository 内の fixture data のみ。依存関係 install 後は live PR、GitHub token、hosted LLM API、external agent service は不要です。 |
| 最初の command | `pnpm run demo:agent-assurance` |
| 任意の artifact check | `pnpm run demo:agent-assurance:check` |
| 主な出力 root | `artifacts/` |
| 最初に開く review surface | `artifacts/review/agent-assurance-demo/assurance-review.md` |
| 補助出力 | `artifacts/agents/agent-assurance-demo/producer-normalization-summary.{json,md}`、`artifacts/assurance/agent-assurance-demo/assurance-summary.{json,md}`、`artifacts/policy/agent-assurance-demo/policy-gate-summary.{json,md}`、`artifacts/verify-lite/agent-assurance-demo/verify-lite-run-summary.json` |
| 証跡の根拠 | `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md` と `docs/product/evidence-packs/evidence-003-self-dogfood/README.md` が、この demo の位置づけを支える observed repository dogfooding path です。 |

Raw log より先に reviewer Markdown を開いてください。Producer output が
report-only finding、claim/evidence status、policy summary、reviewer action に
正規化される流れを確認できます。これは approval、merge authority、live external
pilot、review speed・safety・quality・adoption impact・agent/vendor 優位性の一般
claim ではありません。

### 最小 setup

```bash
corepack enable
corepack prepare pnpm@10.0.0 --activate
pnpm install --frozen-lockfile
pnpm run demo:agent-assurance
```

`pnpm run first-run` は environment/build/verify baseline として有用ですが、初見の
product evidence demo として `demo:agent-assurance` と比較する必要はありません。

Checker は任意かつ report-only です。Demo 実行後の agent-assurance first-run
artifact path を検証するだけで、GitHub、hosted LLM API、external agent service は
呼び出さず、merge gate でもありません。
Demo が artifacts を生成した後にだけ実行します。

```bash
pnpm run demo:agent-assurance:check
```

### 次に読むもの

1. `docs/guides/byo-agent-assurance-quickstart.md` — 15分 walkthrough。
2. `docs/product/EVIDENCE-SPRINT-DOGFOOD-CASE-STUDY-2026-07-01.md` — Evidence Sprint case study。
3. `docs/product/evidence-packs/evidence-003-self-dogfood/README.md` — stable evidence links。
4. `docs/product/EVIDENCE-SPRINT-WEB-API-PILOT-2026-07-01.md` と `docs/product/EVIDENCE-SPRINT-EVENT-DRIVEN-PILOT-2026-07-01.md` — optional domain-preset pilots。
5. `docs/getting-started/REFERENCE-FLOW.md` — real Issue-to-PR assurance path へ進む場合。

Domain preset、formal lane、PR posting helper、high-assurance strict lane は、初回
demo では必須ではなく、risk/profile に応じた optional flow です。

### Troubleshooting

| 症状 | 確認 | 対応 |
| --- | --- | --- |
| `npm install` が失敗またはブロックされる | この repository は pnpm workspace を前提にしています。 | `corepack enable`、`corepack prepare pnpm@10.0.0 --activate`、`pnpm install --frozen-lockfile` を実行します。 |
| `pnpm: command not found` | active な Node.js で Corepack が有効でない可能性があります。 | Node.js 20.11+ を使用し、上記 Corepack commands を実行します。 |
| `artifacts/review/agent-assurance-demo/assurance-review.md` がない | demo が完了していないか artifacts が削除されています。 | `pnpm run demo:agent-assurance` を再実行し、続けて `pnpm run demo:agent-assurance:check` で first-run artifact set を確認します。 |
| review surface を PR に投稿したい | 投稿は first-run demo の範囲外です。 | `docs/guides/byo-agent-assurance-quickstart.md` に従い、`gh auth status` と repository/PR scope を確認するまでは posting helper を dry-run にします。 |
