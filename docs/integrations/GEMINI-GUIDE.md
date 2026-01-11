# Gemini Code Assist Guide (draft)

## 目的
- Gemini Code Assist から ae-framework テンプレを利用し、Spec→Test→Code→Verify を踏むための手順を提供。
- Markdown/JSON 入出力を徹底し、AJV/Schema で検証可能な形に固定する。

## 前提
- リポ構成: `spec/`, `tests/`, `plans/common/*`（汎用テンプレ）、`plans/web-api/*`（Web API + DB リファレンス）
- Gemini からシェルコマンド実行/ファイル編集が可能

## 実行フロー（例）
1. 仕様生成: `plans/common/01-spec.md` を入力し、Spec/BDD/Property の骨子を生成
2. テスト骨子: `plans/common/02-tests.md` を入力し、テストスケルトンを生成（skip許容）
3. 実装: `plans/common/03-impl.md` を入力し、実装を生成
4. 検証: `plans/common/04-verify.md` のコマンドを実行
5. PR: `plans/common/05-pr.md` をもとに PR 本文を作成

## 検証コマンド例
- `pnpm run lint`
- `pnpm run test:fast`
- `pnpm run test:property`
- (任意) `STRYKER_TIME_LIMIT=0 pnpm run pipelines:mutation:quick`

## I/O ポリシー
- 生成先パスを明示し、既存ファイルを安全に上書きする
- JSON/YAML はフォーマットを保ち、スキーマ検証を行う
- PR では Spec/Tests/Cache を明記
- Spec Kit の最小手順は `docs/reference/SPEC-VERIFICATION-KIT-MIN.md` を参照
