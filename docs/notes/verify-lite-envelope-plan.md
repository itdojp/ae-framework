# Verify Lite → Envelope 変換プラン

## 現状整理
- Verify Lite 実行結果は `verify-lite-run-summary.json` に書き出され、スキーマ `schema/verify-lite-run-summary.schema.json` で定義済み。
- `scripts/trace/create-report-envelope.mjs` は任意のサマリーファイル（デフォルトで Verify Lite のもの）をそのまま `summary` フィールドに格納するが、Envelope v1.0 では `traceCorrelation` 等の共通フィールドに寄せる必要あり。
- Agent Builder 連携 (#1047/#1053) では、Verify Lite サマリーを Envelope へ正規化するコンバータ（PR-2）を実装する計画。

## 変換で扱うべき項目
| Verify Lite summary | Envelope v1.0 へのマッピング | 備考 |
| --- | --- | --- |
| `schemaVersion` | `summary.schemaVersion`（保持） | Envelope 内では `summary` にネストしたまま利用 |
| `timestamp` | `generatedAt` / `summary.timestamp` | Envelope の `generatedAt` は生成時刻、Verify Lite の `timestamp` は `summary` に保持 |
| `flags.*` | `summary.flags.*` | そのまま保持 |
| `steps.*` | `summary.steps.*` | ステップ名はキーとして維持 |
| `artifacts.*` | `artifacts` array へ変換 | 存在するパスのみ `type=application/json` + 説明を付与 |
| `tempoLinks` / `trace.traceIds` | `traceCorrelation.traceIds` / `TempoLinks` / `notes` | 既存 `create-report-envelope.mjs` のロジックを流用予定 |

## コンバータ設計
- **入口**: `packages/envelope/src/from-verify-lite.ts`（新規）
  - 引数: `VerifyLiteSummary`（型を同ファイル or `types.ts` に定義）
  - 返値: `Envelope` オブジェクト（v1.0 / `traceCorrelation` を含む）
- **責務**:
  1. Summary の必須フィールド検証（必要に応じて簡易 Validation）
  2. Envelope 固有フィールドの組立
     - `schemaVersion`: `1.0.0`
     - `source`: `verify-lite`
     - `generatedAt`: 現在時刻 or Summary timestamp
     - `traceCorrelation`: runId/commit/branch は呼び出し元から受け取る（引数で `context` を受ける）
  3. アーティファクト配列への正規化（存在しないパスは除外）
  4. Tempo links・notes の付与（`buildTempoLinks` 相当）
- **補助構造**:
  - `packages/envelope/src/types.ts` に Envelope / Context / Artifact などの型。
  - テスト用 Fixture: `fixtures/envelope/from-verify-lite.sample.json` など追加予定。

## テスト戦略
- `packages/envelope/src/from-verify-lite.test.ts`
  - 正常系: 代表的な Verify Lite summary から Envelope を生成し、Vitest snapshot で検証。
  - 省略フィールド: `artifacts.lintLog` が null の場合、出力から除外されるかを確認。
  - Trace/Tempo: summary 側の `traceDomains` などを含む場合のリンク集約を検証。
- `node scripts/ci/validate-json.mjs` を利用し、生成された Envelope が v1.0 スキーマに準拠しているか検証するヘルパを用意。

## 次ステップ（PR-2）
1. `packages/envelope` ディレクトリを作成し、`package.json` or workspace 設定に追加。
2. `from-verify-lite.ts` 実装、型定義、ユーティリティ導入。
3. Vitest + snapshot を追加し、サンプルまとめ。
4. `create-report-envelope.mjs` で新コンバータを呼び出す／もしくは CLI ラッパーを追加。
5. CI に Envelope 生成テストを組み込む（Verify Lite workflow or 別ジョブ）。
