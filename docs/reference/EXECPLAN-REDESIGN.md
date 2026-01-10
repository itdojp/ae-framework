# ExecPlan 再設計（方針と仕分け）

## 目的
- 新ポジショニング（Agentic SDLC Orchestrator & Spec/Verification Kit）に沿って ExecPlan 群を整理する。
- Codex 以外（Antigravity/Gemini 等）からも呼び出しやすい入出力形式を定義する。

## 現状の課題（例）
- 計画が散在し、維持/廃止の区分が不明瞭。
- I/O 形式が統一されておらず、エージェントごとに適合作業が発生。

## 仕分けポリシー
- **維持**: Spec→Test→Code→Verify→PR を一貫でカバーし、入出力が Markdown/JSON のもの。
- **アーカイブ**: 独自ランタイム/IDE 依存、ブラウザ制御、6フェーズ特化の旧プラン。
- **要更新**: コンテキスト/変数名が古いが流用価値があるもの。

## 既存 ExecPlan / Flow インベントリ（2026-01）
| 種別 | 位置 | 仕分け | メモ |
| --- | --- | --- | --- |
| ExecPlan | `plans/web-api/01-05-*.md` | 維持 | Web API + DB リファレンス用の基準テンプレ |
| ExecPlan | `plans/common/01-05-*.md` | 維持 | ドメイン非依存の共通テンプレ（新規） |
| Flow | `docs/flows/web-api-agent.md` | 維持 | エージェント併用の実行手順とトレース |
| Flow | `docs/flows/web-api-manual.md` | 維持 | 人手運用の実行手順とトレース |
| Flow | `docs/flows/agent-builder-flow.md` | 要更新 | Agent Builder 設計の差分を確認中 |

## 新しい標準 ExecPlan セット（草案）
- `plans/web-api/01-05-*.md`（#1195 で追加済み）をベースラインにする。
- 汎用スケルトン（他ドメイン向け）
  - 01-spec: 要件→仕様(BDD/Property)→OpenAPI/JSON Schema
  - 02-tests: Unit/Integration/Property スケルトン
  - 03-impl: 実装スキャフォールド + マイグレーション/シード
  - 04-verify: lint/type/unit/integration/property(+mutation quick)
  - 05-pr: PR 本文テンプレ

## I/O 形式の標準
- 入力: Markdown/JSON を必須。ファイルパスを明記し、上書き禁止領域をコメントで指定。
- 出力: 生成物パスを列挙し、付随するコマンド（lint/test）が実行可能な形で提示。
- メタデータ: 追記先 `docs/flows/*` にログ/Trace欄を確保。

## Antigravity/Gemini などへの展開
- ExecPlan を Markdown で提供し、CLI 以外のエージェントにも渡せるようにする。
- JSON 版のパラメタライズ（例: steps, inputs, outputs）を用意し、将来 API 経由で渡せるようにする（別タスク）。

## TODO
- [x] 既存 ExecPlan の棚卸しリストを作成（維持/アーカイブ/要更新の分類表）
- [x] 汎用スケルトン（01-05）を `plans/common/` に複製し、変数化（projectName, domain 等）
- [ ] 旧6フェーズ系 ExecPlan を `plans/archive/` に移動し、README で非推奨を明記
- [ ] JSON 版 ExecPlan schema をドラフト化（steps/inputs/outputs/commands）
