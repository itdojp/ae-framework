---
docRole: derived
canonicalSource:
- docs/strategy/CODEX-AE-BOUNDARY-VERIFY-FIRST.md
- docs/spec/context-pack.md
- docs/reference/CLI-COMMANDS-REFERENCE.md
lastVerified: '2026-03-10'
---
# Input-Only Spec Repository Pattern（入力のみリポジトリ・パターン）

> Language / 言語: English | 日本語

---

## English (Summary)

This document describes a strict **input-only spec repository** pattern for benchmarking agentic synthesis with ae-framework.

- **Input repo** contains only human-readable specs and fixed assumptions.
- **Machine-readable API contracts** (OpenAPI / JSON Schema / etc.) are treated as **outputs**, regardless of directory name.
- **Tests/CI that assume generated outputs** are also **outputs** and must not be placed in the input repo.
- Use an external **harness** (local runner or CI) to run an *Input Gate* and *Synthesis Gate*, and store generated artifacts in a separate output repo.

---

## 日本語

## 1. 目的

本ドキュメントは、ae-framework を用いた試行/ベンチマークとして「**最小限の仕様（入力）から実装（出力）を生成できること**」を明確化するための、**入力/出力の境界（repository boundary）**を定義します。

主目的は以下です。

- 入力を最小化し、成果物（実装/契約/テスト/CI 等）を **出力として扱う**ことで、試行の再現性と比較可能性を高める
- 仕様→実装の合成プロセス（Synthesis）において、入力側に解答（生成物）が混入することを防ぐ
- 生成物の保管・分析・差分比較を、入力リポジトリと分離して運用可能にする

## 2. 用語

- **入力リポジトリ（Input Spec Repo）**: 合成対象の入力。人間可読な仕様と、上級工程で固定した前提のみを保持する。
- **出力リポジトリ（Output / Artifacts Repo）**: 合成によって得られた生成物（実装/契約/テスト/CI 等）を保持する。
- **ハーネス（Harness）**: 入力を取り込み、ae-framework（＋必要なら Codex CLI）を実行して出力を生成・検証・保存する実行基盤。CI（GitHub Actions 等）またはローカルランナーを含む。

## 3. 不変条件（今回の合意事項）

### 3.1 機械可読な API 契約は「出力」に統一

ディレクトリ名に依らず、次のような **機械可読な API 契約**は **出力（生成物）**として扱います。

- OpenAPI（YAML/JSON）
- JSON Schema
- Protocol Buffers（`.proto`）
- GraphQL SDL
- AsyncAPI など

> 例: `contracts/openapi.yaml`, `schema/*.schema.json`, `spec/openapi/*.openapi.yaml` など、置き場所がどこであっても「機械可読な契約」であれば出力に分類します。

### 3.2 `contracts/**` と `schema/**` は出力（生成物）

実例として頻出する `contracts/**` と `schema/**` は、合成の成果物として扱います（入力リポジトリに置かない）。

### 3.3 契約/スキーマに依存するテスト/CIも出力（生成物）

機械可読契約や生成コードの存在を前提にする以下は、入力に含めません。

- API 契約に依存する conformance テスト
- 生成コード/生成契約の整合を前提としたユニット/統合テスト
- 生成物を前提にする CI ワークフロー（`.github/workflows/*` を含む）

## 4. 入力/出力の配置指針（推奨）

### 4.1 入力リポジトリ（Input Spec Repo）

入力リポジトリに置くもの（例）:

- 人間可読な要求・仕様（Markdown）: `spec/*.md`
- タスク定義/評価観点（ある場合）: `task.md` 等
- 上級工程で固定した前提（対象プラットフォーム、制約、非機能要求、DoD 等）: `assumptions.md` 等
- （Codex CLI を用いる場合）作業指示: `AGENTS.md`

入力リポジトリに置かないもの（禁止）:

- 機械可読な API 契約（OpenAPI/JSON Schema 等）
- 実装コード（`src/` 等）
- テスト（`tests/` 等）
- 生成物を前提にする CI（`.github/workflows/*`）
- 生成物（`contracts/**`, `schema/**` を含む）

### 4.2 出力リポジトリ（Output / Artifacts Repo）

出力リポジトリに置くもの（例）:

- 実装コード、テスト、CI ワークフロー
- 機械可読な API 契約（OpenAPI 等）
- スキーマ（JSON Schema 等）
- 実行ログ、サマリ、レポート（例: `artifacts/**`, `.ae/**`）

## 5. 実行ゲート（概念設計）

入力と出力を分離した場合、CI の役割は「アプリ CI」ではなく、主に次の2系統になります（ハーネス側で実行することを想定）。

### 5.1 Input Gate（入力健全性）

- 入力リポジトリに「出力相当のファイル」が混入していないことの検査
- 仕様の静的検査（例: `ae-framework -- spec validate`, `ae-framework -- spec lint`）
- 前提条件（実行環境/固定した参照）の妥当性確認

### 5.2 Synthesis Gate（合成の実行可能性）

- 入力から合成（生成）が実行できることの検査（実行手順の再現性）
- 最低限の出力が生成されることの検査（例: 実装の雛形、契約、サマリ）
- 生成物の詳細な品質検証（テスト/カバレッジ/セキュリティ等）は、原則として出力側へ分離

## 6. 補足（このパターンの適用範囲）

本パターンは「仕様から実装を合成できること」の検証や、エージェント性能評価（入力最小化）を主目的とするため、通常のプロダクト開発（契約先行で OpenAPI を入力に置く等）とは境界設計が異なります。運用目的に応じて、入力/出力の分類は明示的に合意し、ハーネス側のゲートで継続的に担保してください。

