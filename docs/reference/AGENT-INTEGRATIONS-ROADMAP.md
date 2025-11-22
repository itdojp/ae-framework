# Agent 統合・高度検証 拡張案（#1198）

## 目的
- Codex 以外のエージェント（Antigravity, Gemini Code Assist 等）から ae-framework のテンプレを踏めるよう、利用ガイドと検証パスを整理する。
- 高度検証（TLA+/model checking 等）の入口を示し、コスト/効果を明示する。

## ガイド構成案
- `docs/integrations/ANTIGRAVITY-GUIDE.md` (予定)
- `docs/integrations/GEMINI-GUIDE.md` (予定)
- 共通: I/O 形式（Markdown/JSON）、AJV/スキーマ検証の必須化、成果物配置パス

## 基本ポリシー
- すべてのエージェントに対し「生成先パス」「検証コマンド」を明示して渡す
- JSON/Markdown 以外の生成物は受け取らない（スキーマ検証を必須化）
- PR には Spec/Tests/Cache 情報を必ず記載（テンプレで担保）

## 高度検証（入口）
- TLA+: `docs/TLA+/` のサンプルを利用し、必要に応じて `model checking (TLC)` を手動実行
- Model checking / Alloy: workflow_dispatch で実行可能なテンプレを用意する（別タスク）
- コスト明記: 実行時間、必要リソース、適用シナリオを表形式で整理（TODO）

## TODO
- [ ] Antigravity/Gemini 用ガイドドラフトを追加（セットアップ、実行例、検証手順）
- [ ] workflow_dispatch ベースの model checking テンプレートを追加（実行しない限り CI に影響なし）
- [ ] 高度検証の適用条件/コスト表を作成し docs に記載
