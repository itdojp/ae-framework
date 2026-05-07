---
docRole: ssot
lastVerified: '2026-05-07'
owner: integration-ops
verificationCommand: pnpm -s run check:doc-consistency
---
# Temporal Workflow Adapter Integration PoC

> Language / 言語: English | 日本語

---

## English

### 1. Purpose and boundary

This document defines the optional Temporal Workflow adapter PoC for long-running assurance orchestration.
The adapter is intentionally placed under `examples/temporal-workflow-adapter` and does not change the default GitHub Actions, CLI, MCP, or existing adapter paths.

Boundary rules:

- The source of truth remains the existing JSON contracts, including `verify-lite-run-summary`, `assurance-summary`, `claim-evidence-manifest`, `policy-decision`, and `change-package/v2`.
- Temporal Workflow metadata is additive and is confined to `temporal-run-summary/v1`.
- Temporal.io is written as `Temporal Workflow` or `Temporal.io` when ambiguity with formal-methods temporal logic is possible.
- Non-deterministic work such as file I/O, subprocess execution, and policy-gate invocation is done in Activities, not in the Workflow function.
- The root package does not depend on Temporal SDK packages; the example package owns its own optional dependencies.

### 2. Contract

The adapter sidecar contract is:

- schema: `schema/temporal-run-summary.schema.json`
- sample fixture: `fixtures/temporal/sample.temporal-run-summary.json`
- schemaVersion: `temporal-run-summary/v1`
- typical output: `artifacts/temporal/<scenario>/temporal-run-summary.json`

The summary records:

- `adapter.sdk.packages`: the optional Temporal SDK packages used by the standalone example (`@temporalio/client`, `@temporalio/worker`, `@temporalio/workflow`)
- `execution`: namespace, Workflow type, Workflow ID, Run ID, task queue, status, startedAt, completedAt
- `signals`: awaited and received approval / waiver signals
- `activityResults`: Activity-level artifact references
- `outputArtifacts`: existing assurance and policy artifacts plus the Temporal sidecar
- `history`: CLI / UI pointer to Temporal event history rather than embedded event history
- `restartValidation`: status and evidence references for worker-restart drills

### 3. Local setup

Temporal's TypeScript quickstart states that the SDK requires Node.js 20 or later and that adding Temporal to an existing project uses the `@temporalio/client`, `@temporalio/worker`, and `@temporalio/workflow` packages. It also documents `temporal server start-dev` for local development server startup.

```bash
# Terminal A: start the local Temporal Service and Web UI.
temporal server start-dev

# Terminal B: install only the optional example package dependencies.
pnpm --dir examples/temporal-workflow-adapter install

# Terminal B: start the Worker.
pnpm --dir examples/temporal-workflow-adapter run worker
```

The local service listens on `localhost:7233`; the Web UI is normally available on `http://localhost:8233`.

### 4. Run the fixture scenario

```bash
# Terminal C: start, auto-approve, wait for completion, and print temporal-run-summary/v1.
pnpm --dir examples/temporal-workflow-adapter run start -- \
  --workflow-id ae-assurance-inventory-waiver \
  --scenario inventory-waiver \
  --auto-approve
```

The Workflow calls these Activities:

1. `readOperationInput`
2. `preparePrerequisites`
3. `runVerifyLite`
4. waits for the `approval` Signal
5. `runPolicyGate`
6. `writeTemporalRunSummary`

`runPolicyGate` delegates to `scripts/assurance/run-e2e-scenario.mjs`, so existing assurance contracts remain the canonical producers of fixture artifacts.

### 5. Worker restart drill

Use this drill to verify durable continuation through a Worker process restart:

```bash
# Terminal C: start the Workflow and leave it waiting for approval.
pnpm --dir examples/temporal-workflow-adapter run start -- \
  --workflow-id ae-assurance-restart-demo \
  --scenario inventory-waiver \
  --no-wait

# Terminal B: stop the Worker with CTRL+C, then start it again.
pnpm --dir examples/temporal-workflow-adapter run worker

# Terminal C: deliver the approval / waiver signal after the Worker returns.
pnpm --dir examples/temporal-workflow-adapter run signal:approval -- \
  --workflow-id ae-assurance-restart-demo

# Terminal C: wait for result and review the generated summary.
pnpm --dir examples/temporal-workflow-adapter run result -- \
  --workflow-id ae-assurance-restart-demo
```

The expected outcome is that the Workflow resumes from its event history, receives the `approval` Signal, runs the policy-gate Activity, and writes `artifacts/temporal/inventory-waiver/temporal-run-summary.json`.

### 6. Validation

```bash
pnpm -s exec vitest run tests/contracts/temporal-run-summary-contract.test.ts
node scripts/ci/validate-json.mjs
pnpm -s run check:doc-consistency
```

The example package can also be type-checked after its optional dependencies are installed:

```bash
pnpm --dir examples/temporal-workflow-adapter run typecheck
```

### 7. Operational notes

- Use `TEMPORAL_ADDRESS`, `TEMPORAL_NAMESPACE`, and `TEMPORAL_TASK_QUEUE` to override local defaults.
- `--generated-at` defaults to the Workflow start time; when omitted, generated assurance artifacts skip expected-fixture comparison to avoid timestamp-only drift. Pass it explicitly when deterministic fixture comparison is required.
- `--output-dir` must be a repository-relative path that stays under the repository root.
- Do not add Temporal SDK packages to the root `package.json` for this PoC.
- Treat `temporal-run-summary/v1` as adapter evidence, not as a replacement for `policy-decision/v1` or `claim-evidence-manifest/v1`.
- If a restart drill is performed, set `--restart-validation-status manual-pass` on the start command to record the evidence status in the summary.

### 8. References

- Temporal TypeScript SDK quickstart: <https://docs.temporal.io/develop/typescript/set-up-your-local-typescript>
- Temporal TypeScript message passing: <https://docs.temporal.io/develop/typescript/workflows/message-passing>
- Temporal TypeScript Activities: <https://docs.temporal.io/develop/typescript/activities/basics>
- Temporal TypeScript Workers: <https://docs.temporal.io/develop/typescript/workers/run-worker-process>
- Temporal TypeScript API reference: <https://typescript.temporal.io/>

---

## 日本語

### 1. 目的と境界

この文書は、long-running assurance orchestration のための任意 Temporal Workflow adapter PoC を定義します。
adapter は `examples/temporal-workflow-adapter` に閉じ、既定の GitHub Actions、CLI、MCP、既存 adapter 経路は変更しません。

境界原則:

- source of truth は既存 JSON contract（`verify-lite-run-summary`、`assurance-summary`、`claim-evidence-manifest`、`policy-decision`、`change-package/v2`）です。
- Temporal Workflow 固有 metadata は additive な `temporal-run-summary/v1` に閉じます。
- formal methods の temporal logic と混同し得る文脈では `Temporal Workflow` または `Temporal.io` と表記します。
- file I/O、subprocess 実行、policy-gate 呼び出しなどの非決定的処理は Workflow 本体ではなく Activity 側で実行します。
- root package は Temporal SDK に依存せず、example package が任意依存を所有します。

### 2. 契約

adapter sidecar contract は次のとおりです。

- schema: `schema/temporal-run-summary.schema.json`
- sample fixture: `fixtures/temporal/sample.temporal-run-summary.json`
- schemaVersion: `temporal-run-summary/v1`
- typical output: `artifacts/temporal/<scenario>/temporal-run-summary.json`

summary は以下を記録します。

- `adapter.sdk.packages`: standalone example が利用する任意 Temporal SDK package（`@temporalio/client`、`@temporalio/worker`、`@temporalio/workflow`）
- `execution`: namespace、Workflow type、Workflow ID、Run ID、task queue、status、startedAt、completedAt
- `signals`: 待機した approval / waiver signal と受信済み signal
- `activityResults`: Activity 単位の artifact reference
- `outputArtifacts`: 既存 assurance / policy artifact と Temporal sidecar
- `history`: event history 全文ではなく CLI / UI pointer
- `restartValidation`: worker restart drill の状態と evidence reference

### 3. ローカルセットアップ

Temporal TypeScript quickstart は、SDK が Node.js 20 以降を要求し、既存 project へ追加する場合に `@temporalio/client`、`@temporalio/worker`、`@temporalio/workflow` を使うと説明しています。また local development server の起動手順として `temporal server start-dev` を示しています。

```bash
# Terminal A: local Temporal Service と Web UI を起動します。
temporal server start-dev

# Terminal B: 任意 example package の依存だけをインストールします。
pnpm --dir examples/temporal-workflow-adapter install

# Terminal B: Worker を起動します。
pnpm --dir examples/temporal-workflow-adapter run worker
```

local service は `localhost:7233`、Web UI は通常 `http://localhost:8233` で利用できます。

### 4. fixture scenario 実行

```bash
# Terminal C: start、auto approval、completion wait、temporal-run-summary/v1 出力を行います。
pnpm --dir examples/temporal-workflow-adapter run start -- \
  --workflow-id ae-assurance-inventory-waiver \
  --scenario inventory-waiver \
  --auto-approve
```

Workflow は次の Activity を呼びます。

1. `readOperationInput`
2. `preparePrerequisites`
3. `runVerifyLite`
4. `approval` Signal 待機
5. `runPolicyGate`
6. `writeTemporalRunSummary`

`runPolicyGate` は `scripts/assurance/run-e2e-scenario.mjs` へ委譲するため、既存 assurance contract が fixture artifact の正規 producer であり続けます。

### 5. Worker restart drill

Worker process の再起動後に継続できることを確認する手順です。

```bash
# Terminal C: Workflow を開始し、approval 待機状態にします。
pnpm --dir examples/temporal-workflow-adapter run start -- \
  --workflow-id ae-assurance-restart-demo \
  --scenario inventory-waiver \
  --no-wait

# Terminal B: Worker を CTRL+C で停止し、再度起動します。
pnpm --dir examples/temporal-workflow-adapter run worker

# Terminal C: Worker 復帰後に approval / waiver signal を送信します。
pnpm --dir examples/temporal-workflow-adapter run signal:approval -- \
  --workflow-id ae-assurance-restart-demo

# Terminal C: 結果を待機し、生成された summary を確認します。
pnpm --dir examples/temporal-workflow-adapter run result -- \
  --workflow-id ae-assurance-restart-demo
```

期待結果は、Workflow が event history から再開し、`approval` Signal を受信し、policy-gate Activity を実行し、`artifacts/temporal/inventory-waiver/temporal-run-summary.json` を書き出すことです。

### 6. 検証

```bash
pnpm -s exec vitest run tests/contracts/temporal-run-summary-contract.test.ts
node scripts/ci/validate-json.mjs
pnpm -s run check:doc-consistency
```

任意依存をインストールした後、example package の typecheck も実行できます。

```bash
pnpm --dir examples/temporal-workflow-adapter run typecheck
```

### 7. 運用メモ

- local default を変える場合は `TEMPORAL_ADDRESS`、`TEMPORAL_NAMESPACE`、`TEMPORAL_TASK_QUEUE` を使用します。
- `--generated-at` は既定で Workflow start time を使います。省略した場合、timestamp のみの drift を避けるため、生成された assurance artifact は expected fixture comparison をスキップします。deterministic fixture comparison が必要な場合は明示指定します。
- `--output-dir` は repository root 配下に収まる repository-relative path に限定します。
- この PoC では Temporal SDK package を root `package.json` に追加しません。
- `temporal-run-summary/v1` は adapter evidence であり、`policy-decision/v1` や `claim-evidence-manifest/v1` の置き換えではありません。
- restart drill を実施した場合は、開始コマンドに `--restart-validation-status manual-pass` を指定して evidence status を summary に記録します。
