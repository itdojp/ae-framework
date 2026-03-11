---
docRole: ssot
lastVerified: '2026-03-11'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# OTel標準化・Artifacts出力・検証/ゲート統合設計（Issue #2380）

最終更新: 2026-03-02

## 1. 現状（2026-03-02 時点）

| 観点 | 現行実装 | 確認されたギャップ |
| --- | --- | --- |
| OTel 取り込み | `.github/workflows/spec-generate-model.yml` の `trace-conformance` ジョブが `scripts/trace/fetch-otlp-payload.mjs` で OTLP payload を取得し、`scripts/trace/convert-otlp-kvonce.mjs` で NDJSON へ正規化 | 正規化ルールが `kvonce.event.*` 前提で、ドメイン横断の共通契約が `docs/ci` 観点で未定義 |
| Artifacts 出力 | `trace-conformance` は `artifacts/hermetic-reports/trace/**`、`artifacts/kvonce-trace-summary.json`、`artifacts/kvonce-trace-envelope.json` を出力。`verify-lite` は `artifacts/verify-lite/verify-lite-run-summary.json` と `artifacts/report-envelope.json` を必須生成 | 観測系成果物の命名・配置が `verify-lite` 系と `kvonce` 系で分散し、どこまでを gate 対象にするかが未整理 |
| スキーマ検証 | `.github/workflows/validate-artifacts-ajv.yml`（`pnpm run artifacts:validate`）が `schema/envelope.schema.json` 等を検証し、`enforce-artifacts` で strict 化可能 | `spec-generate-model` で生成される成果物は、PR 実行経路によっては `validate-artifacts` の検証対象にならない |
| 検証/ゲート | `scripts/trace/run-kvonce-conformance.sh` は `kvonce-validation.json` が invalid の場合に exit 1。`policy-gate` は `policy/risk-policy.yml` の `enforce-artifacts -> validate-artifacts / validate` を評価 | `KvOnce Trace Validation` チェックは `policy-gate` の評価対象に未接続。`run-trace` ラベル（旧表記: `run-conformance`）は推奨表示のみで実行トリガー未実装 |
| Required checks | `policy/risk-policy.yml` の required は `verify-lite` と `policy-gate`（branch protection preset で `gate` 併用パターンあり） | OTel/trace 検証を Required に昇格する判断基準と導線が未定義 |

## 2. 非ゴール

- 本設計では、Collector 基盤（Tempo/Jaeger/S3/GCS）のプロダクト選定は扱わない。
- KvOnce 以外のドメイン不変条件（projector/validator の業務ロジック）再設計は扱わない。
- 直ちに branch protection の Required checks を増やすことは行わない（段階導入前提）。

## 3. 設計判断

1. **3層分離で標準化する**  
   OTel payload（入力）/ 正規化イベント（処理）/ レポート封筒＋検証結果（出力）を分離し、各層に責務を固定する。
2. **Artifacts contract を gate の基礎に据える**  
   新規 gate 実装を増やさず、既存の `artifacts:validate` + `validate-report-envelope` + `policy-gate` を接続して段階的に強化する。
3. **ラベル駆動で段階的に厳格化する**  
   既定は report-only を維持し、`enforce-artifacts` など既存ラベルで strict 化し、安定後に Required 化判断へ進む。
4. **既存パス互換を維持する**  
   `artifacts/report-envelope.json` と `artifacts/kvonce-trace-envelope.json` は当面共存し、移行フェーズで統一方針を確定する。
5. **ゲート判定の一次情報を限定する**  
   Required/optional の判定根拠は `policy/risk-policy.yml` と branch protection preset（`.github/branch-protection.main.*.json`）に統一する。

## 4. 段階導入計画（実装順序）

### Phase 0: ベースライン固定（現状可視化）
- この運用設計を SSOT として作成し、CI 導線へ索引追加する。
- `docs` 整合チェックを通し、以後の差分検証基準を固定する。

### Phase 1: OTel 正規化契約の明文化（report-only）
- `kvonce.event.*` と共通イベント項目（`traceId`, `timestamp`, `actor`, `event`）の対応規約を文書化する。
- `spec-generate-model` の OTLP/NDJSON 両経路で、同一の成果物セット（events/projection/validation/envelope）が出ることを確認する。
- この段階では Required 化しない。

### Phase 2: Artifacts 出力契約の統合
- gate 対象成果物（最低: trace envelope、trace validation、verify-lite summary/report-envelope）を明示し、`artifacts:validate` の対象ルールへ反映する。
- `enforce-artifacts` 運用時に、trace 系成果物の欠損/破損が strict で検出される状態にする。

### Phase 3: 検証/ゲート接続（label-gated blocking）
- trace 検証を PR 文脈で確実に起動できるトリガー（既存ラベル運用または dispatch 経路）を定義する。
- `policy-gate` が trace 検証結果を評価できるよう、`policy/risk-policy.yml` の gate mapping を追加する。
- 高リスクPRで対象ラベルが付与された場合のみ blocking とする。

### Phase 4: Required 化判断と昇格
- 連続運用データ（失敗率/復旧時間/再現性）を確認し、Required check 昇格可否を判定する。
- 合意後に branch protection preset を更新し、ロールバック条件（解除手順）を同時定義する。

## 5. 受け入れ基準

- `spec-generate-model` の `trace-conformance` 実行で、OTLP/NDJSON の両ケースに `kvonce-validation.json` と `kvonce-trace-envelope.json` が生成され、`schema/envelope.schema.json` 検証を通過する。
- `enforce-artifacts` 有効時、`pnpm run artifacts:validate -- --strict=true` で対象 artifacts のスキーマ違反を検出できる。
- 高リスクPRに必要ラベルが付与された場合、`policy-gate` が対応 gate check を評価し、未実行/失敗を blocking error として扱える。
- Required checks は Phase 4 完了まで `verify-lite` + `policy-gate`（必要に応じて `gate` 併用）の運用を維持する。

## 6. 関連ファイル（一次情報）

### Workflow
- `.github/workflows/spec-generate-model.yml`
- `.github/workflows/verify-lite.yml`
- `.github/workflows/spec-validation.yml`
- `.github/workflows/validate-artifacts-ajv.yml`
- `.github/workflows/policy-gate.yml`

### Scripts
- `scripts/trace/fetch-otlp-payload.mjs`
- `scripts/trace/convert-otlp-kvonce.mjs`
- `scripts/trace/run-kvonce-conformance.sh`
- `scripts/trace/create-report-envelope.mjs`
- `scripts/ci/validate-artifacts-ajv.mjs`
- `scripts/ci/policy-gate.mjs`

### Policy / Schema / Docs
- `policy/risk-policy.yml`
- `schema/envelope.schema.json`
- `schema/trace-bundle.schema.json`
- `schema/trace-bundle-summary.schema.json`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/trace/kvonce-trace-schema.md`
- `docs/trace/otlp-collector-plan.md`
