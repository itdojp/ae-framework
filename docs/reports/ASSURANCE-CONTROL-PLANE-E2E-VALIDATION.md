---
docRole: derived
canonicalSource:
  - fixtures/assurance-e2e/inventory-waiver/README.md
  - scripts/assurance/run-e2e-scenario.mjs
  - schema/claim-evidence-manifest.schema.json
  - schema/claim-level-summary-v1.schema.json
  - schema/policy-decision-v1.schema.json
  - schema/change-package-v2.schema.json
lastVerified: '2026-05-08'
---

# Assurance Control Plane E2E Validation Report

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This report records the current-head smoke fixture that validates the assurance-control-plane flow from requirement references to claims, evidence, achieved level, policy decision, and a proof-carrying change-package summary.

The fixture is intentionally small and deterministic. It does not claim production assurance for an external system; it verifies that the repository's contracts, renderers, and golden artifacts remain connected.

### 2. Scenario

Fixture root: `fixtures/assurance-e2e/inventory-waiver/`

The inventory-waiver scenario uses three claims and two explicit requirement references.

| Requirement | Claim | State in generated evidence | Purpose |
| --- | --- | --- | --- |
| `REQ-INV-001` | `no-negative-balance` | `model-checked` with missing target-level evidence | Shows that a claim can have model evidence while still remaining below its target assurance level. |
| `REQ-INV-002` | `manual-fraud-review` | `waived` | Shows that a waiver is visible and not treated as a pass. |
| n/a, imported from assurance summary | `no-negative-stock` | `runtime-mitigated` in claim-level summary | Shows that runtime evidence remains a runtime mitigation and is not promoted to proof. |

The scenario includes non-green evidence through:

- `manual-fraud-review`: active waiver / residual risk.
- `no-negative-balance`: A3 target with A2 achieved-level gap retained as missing evidence.
- `no-negative-stock`: runtime mitigation remains distinct from proof.

### 3. Artifact chain

| Step | Artifact | Schema / contract | Reviewer use |
| --- | --- | --- | --- |
| Requirement and intent | `fixtures/assurance-e2e/inventory-waiver/inputs/change-package-v2.json` | `change-package/v2` | Lists `REQ-INV-001`, `REQ-INV-002`, linked claims, validation lanes, waiver, and residual risk. |
| Lightweight verification lane | `expected/verify-lite-run-summary.json` | `verify-lite-run-summary/v1` | Confirms the fixture has a green lightweight verification input. |
| Assurance lane summary | `expected/assurance-summary.json` | `assurance-summary/v1` | Provides evidence for `no-negative-stock`. |
| Evidence manifest | `expected/claim-evidence-manifest.json` | `claim-evidence-manifest/v1` | Collects claim-level evidence, missing evidence, and waiver references. |
| Policy input | `expected/policy-input-v1.json` | `policy-input/v1` | Freezes the policy-gate input for the scenario. |
| Policy decision | `expected/policy-decision-js-v1.json` | `policy-decision/v1` | Confirms report-only assurance result is `waived`. |
| Policy summary | `expected/policy-gate-summary.md` | human-readable summary | PR-comment style policy summary. |
| Achieved-level summary | `expected/claim-level-summary.json` / `.md` | `claim-level-summary/v1` | Shows per-claim target level, achieved level, state, decision, missing evidence, and waiver count. |
| Change-package summary | `expected/change-package-v2.json` / `.md` | `change-package/v2` | Human-reviewable proof-carrying package summary for PR/release input. |

### 4. Smoke command

```bash
pnpm -s run assurance:e2e -- --scenario inventory-waiver
```

For deterministic local output while developing:

```bash
pnpm -s run assurance:e2e -- \
  --scenario inventory-waiver \
  --output-dir artifacts/assurance-e2e/inventory-waiver/latest
```

The runner validates JSON artifacts against schemas and compares generated artifacts with the checked-in golden files. `--output-dir` must remain under the repository root so generated artifact paths stay repo-relative. Intentional contract or renderer changes must use `--update-expected` only after review.

### 5. Current expected result

The expected current-head smoke result is:

- `claim evidence claims: 3`
- `claim-level claims: 3`
- `waived claims: 1`
- `policy assurance result: waived`
- `change-package assurance status: partial`
- `comparison: ok`

### 6. Acceptance coverage

| Requirement | Evidence |
| --- | --- |
| Requirement → claim → evidence → achieved level → policy decision is traceable | `change-package-v2.json`, `claim-evidence-manifest.json`, `claim-level-summary.json`, `policy-decision-js-v1.json`. |
| Includes a non-green case | `manual-fraud-review` waiver and `no-negative-balance` missing target-level evidence. |
| JSON artifacts validate against schemas | `run-e2e-scenario.mjs` validates verify-lite, assurance summary, claim evidence manifest, policy input, policy decision, policy-gate summary, claim-level summary, and change-package v2. |
| Markdown summary is usable as PR/release input | `policy-gate-summary.md`, `claim-level-summary.md`, and `change-package-v2.md`. |
| Smoke validation command is documented | This report and `fixtures/assurance-e2e/inventory-waiver/README.md`. |

### 7. Limits

- This is a fixture-backed smoke, not a heavy formal full run.
- The scenario is intentionally report-only; it verifies representation of waived/missing/runtime-mitigated states, not production enforcement.
- Runtime mitigation is not treated as proof.
- Waiver-backed claims remain distinguishable from satisfied or passed claims.

---

## 日本語

### 1. 目的

このレポートは、current HEAD における assurance control plane の最小 E2E smoke fixture を記録します。対象は、requirement reference から claim、evidence、achieved level、policy decision、proof-carrying change-package summary までの接続です。

この fixture は小さく決定的であり、外部システムの production assurance を主張するものではありません。repo 内の contract、renderer、golden artifact が接続されていることを検証します。

### 2. シナリオ

fixture root: `fixtures/assurance-e2e/inventory-waiver/`

inventory-waiver シナリオは、3 つの claim と 2 つの明示的な requirement reference を使います。

| Requirement | Claim | 生成 evidence 上の状態 | 目的 |
| --- | --- | --- | --- |
| `REQ-INV-001` | `no-negative-balance` | `model-checked` かつ target-level evidence 不足あり | model evidence があっても target assurance level に未達であることを表現する。 |
| `REQ-INV-002` | `manual-fraud-review` | `waived` | waiver が pass ではなく明示的に残ることを表現する。 |
| n/a, assurance summary 由来 | `no-negative-stock` | claim-level summary では `runtime-mitigated` | runtime evidence が proof に昇格されないことを表現する。 |

non-green case は次で表現します。

- `manual-fraud-review`: active waiver / residual risk。
- `no-negative-balance`: A3 target に対して A2 achieved-level gap が missing evidence として残る。
- `no-negative-stock`: runtime mitigation が proof と区別される。

### 3. Artifact chain

| Step | Artifact | Schema / contract | レビュー用途 |
| --- | --- | --- | --- |
| Requirement and intent | `fixtures/assurance-e2e/inventory-waiver/inputs/change-package-v2.json` | `change-package/v2` | `REQ-INV-001`、`REQ-INV-002`、claim、validation lane、waiver、residual risk を示す。 |
| Lightweight verification lane | `expected/verify-lite-run-summary.json` | `verify-lite-run-summary/v1` | fixture の lightweight verification input が green であることを示す。 |
| Assurance lane summary | `expected/assurance-summary.json` | `assurance-summary/v1` | `no-negative-stock` の evidence を提供する。 |
| Evidence manifest | `expected/claim-evidence-manifest.json` | `claim-evidence-manifest/v1` | claim 単位の evidence、missing evidence、waiver reference を集約する。 |
| Policy input | `expected/policy-input-v1.json` | `policy-input/v1` | policy-gate input を固定する。 |
| Policy decision | `expected/policy-decision-js-v1.json` | `policy-decision/v1` | report-only assurance result が `waived` であることを確認する。 |
| Policy summary | `expected/policy-gate-summary.md` | human-readable summary | PR comment 形式の policy summary。 |
| Achieved-level summary | `expected/claim-level-summary.json` / `.md` | `claim-level-summary/v1` | claim ごとの target level、achieved level、状態、decision、missing evidence、waiver 数を示す。 |
| Change-package summary | `expected/change-package-v2.json` / `.md` | `change-package/v2` | PR/release 入力として review 可能な proof-carrying package summary。 |

### 4. Smoke command

```bash
pnpm -s run assurance:e2e -- --scenario inventory-waiver
```

開発中に deterministic output directory を使う場合:

```bash
pnpm -s run assurance:e2e -- \
  --scenario inventory-waiver \
  --output-dir artifacts/assurance-e2e/inventory-waiver/latest
```

runner は JSON artifact を schema validation し、生成結果を checked-in golden file と比較します。`--output-dir` は repository root 配下に限定し、生成 artifact path を repo-relative に保ちます。意図的な contract / renderer 変更のみ、レビュー後に `--update-expected` を使います。

### 5. 現在の期待結果

current HEAD の期待結果は次です。

- `claim evidence claims: 3`
- `claim-level claims: 3`
- `waived claims: 1`
- `policy assurance result: waived`
- `change-package assurance status: partial`
- `comparison: ok`

### 6. Acceptance coverage

| 要件 | Evidence |
| --- | --- |
| Requirement → claim → evidence → achieved level → policy decision を追跡できる | `change-package-v2.json`, `claim-evidence-manifest.json`, `claim-level-summary.json`, `policy-decision-js-v1.json`。 |
| non-green case を含む | `manual-fraud-review` の waiver と `no-negative-balance` の target-level evidence 不足。 |
| JSON artifact が schema validation される | `run-e2e-scenario.mjs` が verify-lite、assurance summary、claim evidence manifest、policy input、policy decision、policy-gate summary、claim-level summary、change-package v2 を検証する。 |
| Markdown summary が PR/release input として使える | `policy-gate-summary.md`, `claim-level-summary.md`, `change-package-v2.md`。 |
| Smoke validation command が文書化される | このレポートと `fixtures/assurance-e2e/inventory-waiver/README.md`。 |

### 7. 制約

- これは fixture-backed smoke であり、heavy formal full run ではありません。
- シナリオは report-only であり、waived / missing / runtime-mitigated state の表現を検証するもので、production enforcement を主張しません。
- runtime mitigation は proof として扱いません。
- waiver-backed claim は satisfied / passed claim と区別します。
