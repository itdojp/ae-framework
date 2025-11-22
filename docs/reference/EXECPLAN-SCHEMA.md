# ExecPlan JSON Schema (draft)

- Schema file: `schemas/execplan.schema.json`
- 目的: ExecPlan を Markdown 以外（API/他エージェント）から扱えるように最小構造を定義。

## フィールド概要
- `id`: 任意ID
- `title`: 計画名
- `description`: 概要（任意）
- `inputs`: 参照するファイル/コンテキストのパス配列
- `outputs`: 生成/更新が期待されるファイルパス配列
- `steps`: 手順配列
  - `title` (必須)
  - `description` (任意)
  - `commands`: 実行コマンド列（任意）

## 運用方針
- Markdown版 ExecPlan と同じ内容を、この Schema に沿った JSON でも提供することで、Antigravity/Gemini 等からの機械利用を容易にする。
- 必須フィールドは `title` と `steps` のみ。必要に応じて拡張予定。
