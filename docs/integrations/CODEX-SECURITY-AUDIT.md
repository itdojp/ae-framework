---
docRole: derived
canonicalSource:
  - package.json
  - docs/reference/CONTRACT-CATALOG.md
  - fixtures/security-assurance/cache-key/README.md
lastVerified: '2026-05-08'
---

# CodeX Security Assurance Audit Runbook

> 🌍 Language / 言語: English | 日本語

---

## English

This runbook describes how to implement and operate the ae-framework **Security Assurance Lane** from Codex / CodeX without relying on external LLM calls in the MVP path.

The lane is an assurance-control-plane workflow. It turns specification-derived security expectations into schema-validated artifacts, links those expectations to candidate source locations, generates proof-attempt audit evidence, classifies candidates through narrow review gates, and then feeds the results into assurance summaries and claim-evidence manifests.

It is **not** a vulnerability disclosure automation system and it is **not** an exploit generator.

## Lane position in ae-framework

Security Assurance Lane fits between specification evidence and policy/PR evidence aggregation:

```text
specification / design / audit scope
  -> security-claim/v1 + security-threat-model/v1 + security-audit-scope/v1
  -> security-code-map/v1
  -> optional security-entrypoint-map/v1
  -> security-audit-task-bundle/v1 + security-finding/v1 candidates
  -> security-review/v1 three-gate classification
  -> assurance-summary/v1 + claim-evidence-manifest/v1
  -> policy-gate report-only summaries and PR summaries
```

Key responsibilities:

- keep security expectations anchored to explicit claims, scope, and trust boundaries;
- keep every intermediate output JSON-first and schema-validated;
- preserve proof-attempt evidence so reviewers can see why a candidate was raised;
- classify candidates through Dead Code, Trust Boundary, and Scope gates before treating them as assurance evidence;
- optionally pass `security-entrypoint-map/v1` evidence to make Trust Boundary rationales explicit without requiring a full call graph;
- keep unconfirmed candidates separate from confirmed vulnerabilities.

## Recommended issue implementation order

Use this order when asking Codex to implement or verify the lane in small PRs:

| Order | Issue | Slice | Main deliverables |
|---:|---|---|---|
| 1 | #3258 | Security claim / threat model / audit scope contracts | `schema/security-claim-v1.schema.json`, `schema/security-threat-model-v1.schema.json`, `schema/security-audit-scope-v1.schema.json`, fixtures, contract catalog |
| 2 | #3260 | Security finding / review contracts | `schema/security-finding-v1.schema.json`, `schema/security-review-v1.schema.json`, candidate/review semantics |
| 3 | #3259 | SPECA-compatible import | `ae security import-speca`, SPECA-like fixture conversion, import summary |
| 4 | #3261 | Spec-to-security-claim extractor | `ae security extract-claims`, explicit `SEC-CLAIM` Markdown extraction |
| 5 | #3262 | Code-map pre-resolution | `ae security map-code`, `security-code-map/v1`, scoped candidate locations |
| 6 | #3263 | Proof-attempt audit producer | `ae security audit`, `security-audit-task-bundle/v1`, fixture-backed candidate findings |
| 7 | #3264 | Three-gate security review | `ae security review`, Dead Code / Trust Boundary / Scope classification |
| 8 | #3265 | Assurance integration | security inputs in `assurance-summary/v1`, `claim-evidence-manifest/v1`, policy/PR summaries |
| 9 | #3266 | Fixture / golden scenario | `fixtures/security-assurance/cache-key/`, `pnpm run test:security-assurance` |
| 10 | #3267 | Codex runbook | this document and links from CodeX integration docs |

Codex should keep each PR focused on one row unless the repository owner explicitly asks for a larger consolidation.

## Common Codex constraints

Use these constraints at the start of every Codex task touching this lane:

```text
- Keep all new outputs JSON-first and schema-validated.
- Add or update fixtures before implementing complex logic.
- Do not call external LLMs, scanners, or network services in tests.
- Treat all generated findings as candidate findings unless explicitly reviewed.
- Do not generate exploit instructions, weaponized PoC, or real-world attack automation.
- Prefer deterministic MVP behavior over broad speculative automation.
- Preserve existing schemas and fixture compatibility unless the issue explicitly asks for a contract change.
- Run the narrowest relevant tests first, then schema/doc checks before opening or updating the PR.
```

## Schema-change workflow

When a PR changes any `schema/security-*.schema.json` file or a security field in `claim-evidence-manifest/v1` / `assurance-summary/v1`:

1. Update the schema and keep `$id`, `title`, `schemaVersion`, and required-field semantics explicit.
2. Update the matching fixture(s):
   - `fixtures/security-assurance/sample.*.json`
   - `fixtures/security-assurance/cache-key/expected/*.json` when the golden scenario shape changes
   - downstream assurance fixtures if `assurance-summary/v1` or `claim-evidence-manifest/v1` changes
3. Update semantic validation when applicable:
   - `scripts/ci/lib/security-assurance-contract.mjs`
   - `scripts/ci/lib/claim-evidence-manifest-contract.mjs`
4. Update contract tests:
   - `tests/contracts/security-assurance-contract.test.ts`
   - `tests/contracts/claim-evidence-manifest-contract.test.ts` when assurance integration changes
5. Update contract documentation:
   - `docs/reference/CONTRACT-CATALOG.md`
   - this runbook if commands or artifact semantics change
6. Run representative validation:

```bash
pnpm -s run check:schemas
node scripts/ci/validate-json.mjs
pnpm -s exec vitest run tests/contracts/security-assurance-contract.test.ts --reporter dot
```

If the schema change intentionally updates the golden scenario, also run the fixture update workflow below.

## Fixture / golden scenario workflow

The canonical deterministic scenario is `fixtures/security-assurance/cache-key/`.

Use it for regression checks:

```bash
pnpm -s run test:security-assurance
```

Generate actual artifacts without comparing to expected output:

```bash
node scripts/security/run-security-assurance-fixture.mjs \
  --scenario cache-key \
  --output-dir artifacts/security-assurance/cache-key/manual-check \
  --no-compare
```

Update expected artifacts only after reviewing the diff and confirming the behavior change is intentional:

```bash
node scripts/security/run-security-assurance-fixture.mjs \
  --scenario cache-key \
  --update-expected

git diff -- fixtures/security-assurance/cache-key/expected
```

A fixture PR should explain why each changed expected artifact is intentional. Do not update goldens merely to make a failing comparison pass.

## MVP execution without external LLM calls

The current MVP path is deterministic and fixture-backed. It does not call an external LLM.

The fixture runner is the safest complete command:

```bash
pnpm -s run test:security-assurance
```

For step-by-step operation, run from the repository root. The `GENERATED_AT` value makes artifacts reproducible.

```bash
GENERATED_AT=2026-05-07T00:00:00.000Z
SECURITY_OUT=artifacts/security
SCENARIO=fixtures/security-assurance/cache-key

mkdir -p "$SECURITY_OUT"
cp "$SCENARIO/inputs/security-audit-scope.json" "$SECURITY_OUT/security-audit-scope.json"
cp "$SCENARIO/inputs/security-threat-model.json" "$SECURITY_OUT/security-threat-model.json"

pnpm -s run security:extract-claims -- \
  --spec "$SCENARIO/inputs/spec.md" \
  --out "$SECURITY_OUT" \
  --generated-at "$GENERATED_AT"

pnpm -s run security:map-code -- \
  --claims "$SECURITY_OUT/security-claims.json" \
  --scope "$SECURITY_OUT/security-audit-scope.json" \
  --target "$SCENARIO/inputs/target" \
  --out "$SECURITY_OUT" \
  --generated-at "$GENERATED_AT"

pnpm -s run security:proof-audit -- \
  --claims "$SECURITY_OUT/security-claims.json" \
  --code-map "$SECURITY_OUT/security-code-map.json" \
  --scope "$SECURITY_OUT/security-audit-scope.json" \
  --out "$SECURITY_OUT" \
  --response-fixture "$SCENARIO/inputs/security-audit-responses.json" \
  --generated-at "$GENERATED_AT"

ENTRYPOINT_MAP_ARGS=()
if [ -f "$SECURITY_OUT/security-entrypoint-map.json" ]; then
  ENTRYPOINT_MAP_ARGS=(--entrypoint-map "$SECURITY_OUT/security-entrypoint-map.json")
fi

pnpm -s run security:review -- \
  --findings "$SECURITY_OUT/security-findings.json" \
  --scope "$SECURITY_OUT/security-audit-scope.json" \
  --code-map "$SECURITY_OUT/security-code-map.json" \
  "${ENTRYPOINT_MAP_ARGS[@]}" \
  --out "$SECURITY_OUT" \
  --generated-at "$GENERATED_AT"

node scripts/assurance/aggregate-lanes.mjs \
  --assurance-profile "$SCENARIO/inputs/assurance-profile.json" \
  --security-claims "$SECURITY_OUT/security-claims.json" \
  --security-findings "$SECURITY_OUT/security-findings.json" \
  --security-review "$SECURITY_OUT/security-review.json" \
  --output-json "$SECURITY_OUT/assurance-summary.json" \
  --output-md "$SECURITY_OUT/assurance-summary.md"

node scripts/assurance/build-claim-evidence-manifest.mjs \
  --assurance-summary "$SECURITY_OUT/assurance-summary.json" \
  --security-claims "$SECURITY_OUT/security-claims.json" \
  --security-findings "$SECURITY_OUT/security-findings.json" \
  --security-review "$SECURITY_OUT/security-review.json" \
  --output-json "$SECURITY_OUT/claim-evidence-manifest.json" \
  --output-md "$SECURITY_OUT/claim-evidence-manifest.md" \
  --generated-at "$GENERATED_AT"
```

When a deterministic `symbol-index/v1` artifact is available, add it to the mapping step as optional evidence:

```bash
pnpm -s run security:map-code -- \
  --claims "$SECURITY_OUT/security-claims.json" \
  --scope "$SECURITY_OUT/security-audit-scope.json" \
  --target "$SCENARIO/inputs/target" \
  --symbol-index artifacts/code/symbol-index.json \
  --out "$SECURITY_OUT" \
  --generated-at "$GENERATED_AT"
```

`--symbol-index` prioritizes matching against symbol name, signature, documentation, and tags, while preserving the existing keyword scan as the fallback path.

After running this sequence, validate the output with:

```bash
node scripts/ci/validate-json.mjs
pnpm -s run check:schemas
```

If you prefer the built CLI after `pnpm run build`, replace `pnpm -s run security:<name> -- ...` with `node dist/src/cli/index.js security <subcommand> ...`.

## Candidate finding vs confirmed vulnerability

Security Assurance Lane uses conservative terminology:

- `security-finding/v1` emitted by `ae security audit` is a **candidate finding**.
- `security-review/v1` with `result=needs-human-review` means the candidate is unresolved; it is not confirmed.
- `security-entrypoint-map/v1` is optional Trust Boundary evidence. It records entrypoint reachability hints only; it is not a complete call graph, dataflow proof, or exploitability confirmation.
- `result=out-of-scope` or `result=rejected` records the review classification and should remain traceable in evidence.
- A vulnerability becomes confirmed only through the repository security process, human validation, and responsible disclosure handling described in `SECURITY.md`.

Do not describe a candidate as exploitable or confirmed unless that separate process has completed.

## Safety, scope, and responsible disclosure

Codex tasks for this lane must stay inside the authorized repository and fixture scope:

- Use local fixtures, project-owned source, and documented audit scopes only.
- Respect bug-bounty or repository security-policy scope when applying the workflow to a real target.
- Do not include secrets, private customer data, or unrelated proprietary code in artifacts.
- Do not send private code or security artifacts to an external LLM or external scanner unless an authorized operator explicitly approves that data flow.
- Do not generate exploit chains, credential theft steps, persistence logic, or real-world attack automation.
- When a finding may be real, stop autonomous merge progression for the affected change and follow `SECURITY.md`.

## Representative verification commands

Use the narrowest relevant checks after each change, then broaden before PR review/merge:

```bash
pnpm -s run test:security-assurance
pnpm -s exec vitest run tests/contracts/security-assurance-contract.test.ts tests/scripts/security-assurance-fixture.test.ts --reporter dot
node scripts/ci/validate-json.mjs
pnpm -s run check:schemas
pnpm -s run check:doc-consistency
pnpm -s run build
```

For TypeScript producer changes, add:

```bash
pnpm -s run types:check
```

Docs-only runbook changes should at minimum run `pnpm -s run check:doc-consistency` and, when dependencies are installed, the security-assurance fixture check if command examples or fixture semantics changed.

---

## 日本語

この runbook は、Codex / CodeX から ae-framework の **Security Assurance Lane** を実装・運用するための手順をまとめたものです。MVP の実行経路では外部 LLM 呼び出しを前提にしません。

この lane は assurance control plane の一部です。仕様由来のセキュリティ期待値を schema validation 済み artifact にし、実装上の候補位置へ接続し、proof-attempt audit の証跡を作り、狭い review gate で candidate を分類し、assurance summary / claim-evidence manifest へ接続します。

これは vulnerability disclosure の自動化でも、exploit generator でもありません。

## ae-framework 内での位置づけ

Security Assurance Lane は、仕様証跡と policy / PR 証跡集約の間に位置します。

```text
仕様 / 設計 / audit scope
  -> security-claim/v1 + security-threat-model/v1 + security-audit-scope/v1
  -> security-code-map/v1
  -> optional security-entrypoint-map/v1
  -> security-audit-task-bundle/v1 + security-finding/v1 candidate
  -> security-review/v1 の3-gate分類
  -> assurance-summary/v1 + claim-evidence-manifest/v1
  -> policy-gate report-only summary / PR summary
```

主な責務は次の通りです。

- security expectation を明示的な claim / scope / trust boundary に固定する
- 中間出力を JSON-first かつ schema validation 済みにする
- candidate が生成された理由を proof-attempt evidence として保持する
- candidate を assurance evidence として扱う前に Dead Code / Trust Boundary / Scope gate で分類する
- full call graph を必須化せず、optional な `security-entrypoint-map/v1` evidence で Trust Boundary rationale を具体化する
- 未確認 candidate と confirmed vulnerability を混同しない

## 推奨 issue 実装順

Codex に小さな PR 単位で依頼する場合は、次の順序を使います。

| 順序 | Issue | 作業単位 | 主な成果物 |
|---:|---|---|---|
| 1 | #3258 | security claim / threat model / audit scope 契約 | `schema/security-claim-v1.schema.json`, `schema/security-threat-model-v1.schema.json`, `schema/security-audit-scope-v1.schema.json`, fixtures, contract catalog |
| 2 | #3260 | security finding / review 契約 | `schema/security-finding-v1.schema.json`, `schema/security-review-v1.schema.json`, candidate / review semantics |
| 3 | #3259 | SPECA-compatible import | `ae security import-speca`, SPECA-like fixture 変換, import summary |
| 4 | #3261 | spec-to-security-claim extractor | `ae security extract-claims`, 明示 `SEC-CLAIM` Markdown 抽出 |
| 5 | #3262 | code-map pre-resolution | `ae security map-code`, `security-code-map/v1`, scope 内 candidate location |
| 6 | #3263 | proof-attempt audit producer | `ae security audit`, `security-audit-task-bundle/v1`, fixture-backed candidate finding |
| 7 | #3264 | 3-gate security review | `ae security review`, Dead Code / Trust Boundary / Scope 分類 |
| 8 | #3265 | assurance 連携 | `assurance-summary/v1`, `claim-evidence-manifest/v1`, policy / PR summary への security 入力連携 |
| 9 | #3266 | fixture / golden scenario | `fixtures/security-assurance/cache-key/`, `pnpm run test:security-assurance` |
| 10 | #3267 | Codex runbook | 本ドキュメントと CodeX integration docs からのリンク |

リポジトリ owner が明示的に統合を依頼しない限り、1 PR は 1 行分の scope に限定します。

## Codex 共通制約

この lane に触れる Codex task の冒頭には、次の制約を置きます。

```text
- Keep all new outputs JSON-first and schema-validated.
- Add or update fixtures before implementing complex logic.
- Do not call external LLMs, scanners, or network services in tests.
- Treat all generated findings as candidate findings unless explicitly reviewed.
- Do not generate exploit instructions, weaponized PoC, or real-world attack automation.
- Prefer deterministic MVP behavior over broad speculative automation.
- Preserve existing schemas and fixture compatibility unless the issue explicitly asks for a contract change.
- Run the narrowest relevant tests first, then schema/doc checks before opening or updating the PR.
```

## schema 変更時の手順

`schema/security-*.schema.json`、または `claim-evidence-manifest/v1` / `assurance-summary/v1` の security field を変更する場合は、次を同一 PR に含めます。

1. schema を更新し、`$id`、`title`、`schemaVersion`、required field の意味を明確にする。
2. 対応 fixture を更新する。
   - `fixtures/security-assurance/sample.*.json`
   - golden scenario の shape が変わる場合は `fixtures/security-assurance/cache-key/expected/*.json`
   - `assurance-summary/v1` または `claim-evidence-manifest/v1` が変わる場合は downstream assurance fixtures
3. 必要に応じて semantic validation を更新する。
   - `scripts/ci/lib/security-assurance-contract.mjs`
   - `scripts/ci/lib/claim-evidence-manifest-contract.mjs`
4. contract test を更新する。
   - `tests/contracts/security-assurance-contract.test.ts`
   - assurance 連携が変わる場合は `tests/contracts/claim-evidence-manifest-contract.test.ts`
5. contract documentation を更新する。
   - `docs/reference/CONTRACT-CATALOG.md`
   - command または artifact semantics が変わる場合は本 runbook
6. 代表検証を実行する。

```bash
pnpm -s run check:schemas
node scripts/ci/validate-json.mjs
pnpm -s exec vitest run tests/contracts/security-assurance-contract.test.ts --reporter dot
```

schema 変更により golden scenario の出力が意図的に変わる場合は、次の fixture 更新手順も実行します。

## fixture / golden scenario 変更時の手順

標準の deterministic scenario は `fixtures/security-assurance/cache-key/` です。

回帰確認:

```bash
pnpm -s run test:security-assurance
```

expected と比較せず actual artifact だけ生成する場合:

```bash
node scripts/security/run-security-assurance-fixture.mjs \
  --scenario cache-key \
  --output-dir artifacts/security-assurance/cache-key/manual-check \
  --no-compare
```

expected artifact の更新は、差分を確認し、意図した挙動変更であることを確認してから実行します。

```bash
node scripts/security/run-security-assurance-fixture.mjs \
  --scenario cache-key \
  --update-expected

git diff -- fixtures/security-assurance/cache-key/expected
```

golden の失敗を単に通す目的で expected を更新してはいけません。PR では、各 expected artifact の変更理由を説明します。

## 外部 LLM を使わない MVP 実行手順

現行 MVP は deterministic かつ fixture-backed です。外部 LLM は呼びません。

完全な実行は fixture runner を使うのが最も安全です。

```bash
pnpm -s run test:security-assurance
```

段階的に確認する場合は、repository root から次を実行します。`GENERATED_AT` は再現性のための固定 timestamp です。

```bash
GENERATED_AT=2026-05-07T00:00:00.000Z
SECURITY_OUT=artifacts/security
SCENARIO=fixtures/security-assurance/cache-key

mkdir -p "$SECURITY_OUT"
cp "$SCENARIO/inputs/security-audit-scope.json" "$SECURITY_OUT/security-audit-scope.json"
cp "$SCENARIO/inputs/security-threat-model.json" "$SECURITY_OUT/security-threat-model.json"

pnpm -s run security:extract-claims -- \
  --spec "$SCENARIO/inputs/spec.md" \
  --out "$SECURITY_OUT" \
  --generated-at "$GENERATED_AT"

pnpm -s run security:map-code -- \
  --claims "$SECURITY_OUT/security-claims.json" \
  --scope "$SECURITY_OUT/security-audit-scope.json" \
  --target "$SCENARIO/inputs/target" \
  --out "$SECURITY_OUT" \
  --generated-at "$GENERATED_AT"

pnpm -s run security:proof-audit -- \
  --claims "$SECURITY_OUT/security-claims.json" \
  --code-map "$SECURITY_OUT/security-code-map.json" \
  --scope "$SECURITY_OUT/security-audit-scope.json" \
  --out "$SECURITY_OUT" \
  --response-fixture "$SCENARIO/inputs/security-audit-responses.json" \
  --generated-at "$GENERATED_AT"

ENTRYPOINT_MAP_ARGS=()
if [ -f "$SECURITY_OUT/security-entrypoint-map.json" ]; then
  ENTRYPOINT_MAP_ARGS=(--entrypoint-map "$SECURITY_OUT/security-entrypoint-map.json")
fi

pnpm -s run security:review -- \
  --findings "$SECURITY_OUT/security-findings.json" \
  --scope "$SECURITY_OUT/security-audit-scope.json" \
  --code-map "$SECURITY_OUT/security-code-map.json" \
  "${ENTRYPOINT_MAP_ARGS[@]}" \
  --out "$SECURITY_OUT" \
  --generated-at "$GENERATED_AT"

node scripts/assurance/aggregate-lanes.mjs \
  --assurance-profile "$SCENARIO/inputs/assurance-profile.json" \
  --security-claims "$SECURITY_OUT/security-claims.json" \
  --security-findings "$SECURITY_OUT/security-findings.json" \
  --security-review "$SECURITY_OUT/security-review.json" \
  --output-json "$SECURITY_OUT/assurance-summary.json" \
  --output-md "$SECURITY_OUT/assurance-summary.md"

node scripts/assurance/build-claim-evidence-manifest.mjs \
  --assurance-summary "$SECURITY_OUT/assurance-summary.json" \
  --security-claims "$SECURITY_OUT/security-claims.json" \
  --security-findings "$SECURITY_OUT/security-findings.json" \
  --security-review "$SECURITY_OUT/security-review.json" \
  --output-json "$SECURITY_OUT/claim-evidence-manifest.json" \
  --output-md "$SECURITY_OUT/claim-evidence-manifest.md" \
  --generated-at "$GENERATED_AT"
```

deterministic な `symbol-index/v1` artifact がある場合は、mapping step に optional evidence として追加します。

```bash
pnpm -s run security:map-code -- \
  --claims "$SECURITY_OUT/security-claims.json" \
  --scope "$SECURITY_OUT/security-audit-scope.json" \
  --target "$SCENARIO/inputs/target" \
  --symbol-index artifacts/code/symbol-index.json \
  --out "$SECURITY_OUT" \
  --generated-at "$GENERATED_AT"
```

`--symbol-index` は symbol name / signature / documentation / tags を優先して照合し、該当 symbol がない場合は既存の keyword scan に fallback します。

実行後は次を確認します。

```bash
node scripts/ci/validate-json.mjs
pnpm -s run check:schemas
```

`pnpm run build` 後に built CLI を使う場合は、`pnpm -s run security:<name> -- ...` を `node dist/src/cli/index.js security <subcommand> ...` に置き換えます。

## candidate finding と confirmed vulnerability の区別

Security Assurance Lane では、用語を保守的に扱います。

- `ae security audit` が出力する `security-finding/v1` は **candidate finding** です。
- `security-review/v1` の `result=needs-human-review` は未解決 candidate を示します。confirmed ではありません。
- `security-entrypoint-map/v1` は optional な Trust Boundary evidence です。entrypoint reachability hint のみを記録し、完全な call graph、dataflow proof、exploitability confirmation ではありません。
- `result=out-of-scope` または `result=rejected` は review 分類であり、証跡として追跡可能なまま残します。
- vulnerability が confirmed になるのは、`SECURITY.md` に記載された repository security process、人手検証、responsible disclosure 対応が完了した場合だけです。

この別プロセスが完了していない candidate を、exploitable または confirmed と表現しないでください。

## Safety / scope / responsible disclosure

この lane の Codex task は、許可された repository と fixture scope の範囲に限定します。

- local fixture、project-owned source、明文化された audit scope のみを使う。
- 実対象へ適用する場合は、bug bounty scope または repository security-policy scope を尊重する。
- secrets、顧客データ、無関係な proprietary code を artifact に含めない。
- 権限のある operator が明示承認しない限り、private code や security artifact を外部 LLM / 外部 scanner に送信しない。
- exploit chain、credential theft、persistence logic、実運用攻撃自動化を生成しない。
- 実在する可能性がある finding を見つけた場合は、対象変更の autonomous merge progression を止め、`SECURITY.md` に従う。

## 代表検証コマンド

変更直後は最小の関連 check を実行し、PR review / merge 前に広げます。

```bash
pnpm -s run test:security-assurance
pnpm -s exec vitest run tests/contracts/security-assurance-contract.test.ts tests/scripts/security-assurance-fixture.test.ts --reporter dot
node scripts/ci/validate-json.mjs
pnpm -s run check:schemas
pnpm -s run check:doc-consistency
pnpm -s run build
```

TypeScript producer を変更した場合は、次も追加します。

```bash
pnpm -s run types:check
```

docs-only の runbook 変更では、少なくとも `pnpm -s run check:doc-consistency` を実行します。command example や fixture semantics を変えた場合は、依存関係が導入済みの環境で `pnpm -s run test:security-assurance` も実行します。
