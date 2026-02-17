# Repository Layout Policy (Issue #2031 / Phase 0)

最終更新: 2026-02-17

## 1. 目的

本ポリシーは、ae-framework のリポジトリ配置を標準化し、次の問題を防止することを目的とする。

- ルート直下への一時生成物の蓄積
- 参照しづらいディレクトリ構成
- 「削除してよいファイル」と「保守対象」の判別コスト増大

## 2. 基本原則

1. **ルート直下は最小化する**  
   ルートには「プロジェクトメタ情報」「ビルド設定」「主要エントリ」のみを置く。
2. **生成物は生成物ディレクトリへ集約する**  
   実行時に生成されるファイルは `artifacts/`・`reports/`・`coverage/`・`temp-reports/` 配下に限定する。
3. **再生成可能なものは原則コミットしない**  
   例外は「契約成果物（fixtures / golden / reference snapshot）」として明示されたもののみ。
4. **1 PR = 1責務で整理する**  
   削除、移動、参照更新、CIガード追加を同一PRに混在させない。

## 3. ルート配置ポリシー

### 3.1 ルート配置を許容する項目

- メタ/規約: `README.md`, `LICENSE`, `CONTRIBUTING.md`, `SECURITY.md`, `AGENTS.md`
- パッケージ/ビルド: `package.json`, `pnpm-lock.yaml`, `pnpm-workspace.yaml`, `tsconfig.json`, `eslint.config.js`
- 開発設定: `.github/`, `.devcontainer/`, `.ae/`, `.gitignore` など dotfiles
- ソース/テスト/仕様: `src/`, `tests/`, `spec/`, `schema/`, `docs/`
- 補助ディレクトリ: `scripts/`, `config/`, `configs/`, `packages/`, `apps/`, `samples/`, `fixtures/`
- 運用成果物（追跡対象のみ）: `artifacts/`（契約済みファイルに限定）

### 3.2 ルート配置を禁止する項目（原則）

- 単発実行生成物:
  - `cegis-report-*.json`
  - `generated-*.json`
  - `filtered-test.json`, `parallel-test.json`, `run-suite.json`, `run-test.json`, `workflow-test.json`
  - `conformance-results.json`, `verify-lite-lint-summary.json`
- 実行キャッシュ/一時物:
  - `node_modules/`, `coverage/`, `test-results/`, `test-results-run/`, `tmp/`
- 日次/手動検証メモの生ファイル（ルート直下）

## 4. 生成物マップ（Phase 0時点）

| 種別 | 代表コマンド/実行経路 | 代表出力 | 取扱い |
|---|---|---|---|
| CEGISレポート | `src/cegis/auto-fix-engine.ts` | `cegis-report-*.json` (root) | ルート禁止。`temp-reports/cegis-archives/` へ退避または削除 |
| Conformance結果 | `ae conformance verify` | `conformance-results.json` | ルート禁止。`artifacts/` か `temp-reports/` へ |
| Integration CLI生成物 | integration系CLI/tests | `generated-*.json`, `run-*.json` など | ルート禁止。テスト実行後に削除 |
| Verify Lite lint要約 | `scripts/ci/run-verify-lite-local.sh` | `verify-lite-lint-summary.json` | ルート禁止。`reports/lint/` 優先 |
| Coverage | `pnpm run coverage`, `pnpm run test:coverage` | `coverage/` | 非追跡（生成物） |
| レポート集約 | quality/verify系 | `reports/`, `artifacts/hermetic-reports/` | 原則非追跡（必要成果物のみ残す） |

## 5. 分類ルール（safe-remove / needs-review / keep）

### safe-remove

- `.gitignore` で無視される再生成可能ファイル
- CI/ローカル再実行で復元できるキャッシュ/中間成果物

### needs-review

- `artifacts/` のうち追跡済みで参照されるファイル
- `plans/`, `examples/`, `proofs/` 等のドキュメント的資産
- 参照関係が不明な過去検証ログ

### keep

- `src/`, `tests/`, `docs/` などの一次ソース
- リリース・ビルド・CIで利用する設定ファイル

## 6. 運用ルール

1. 新規コマンドを追加する際は、出力先を `artifacts/` か `reports/` に固定する。  
2. ルート直下へ生成する実装は受け入れない（既存実装は段階的に解消）。  
3. Cleanupコマンド（`pnpm run clean:project`）で除去できることを保証する。  
4. Phase 3で「ルート汚染検知」をCI必須ゲート化する。  

## 7. 次アクション（Phase 1向け）

- ルート直下の生成物パターンを発生源単位で修正
- `needs-review` 対象をサブフォルダ再配置するPRを分割投入
- 配置違反を検知するスクリプト（例: `scripts/ci/check-root-layout.mjs`）を追加
