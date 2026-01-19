# Copilot Review Gate

目的: PR をマージする前に、GitHub Copilot によるコードレビューが存在し、その指摘（スレッド）が解決済みであることを必須化します。

## 仕組み
- Workflow: `.github/workflows/copilot-review-gate.yml`
- 動作: PRのレビュー一覧とレビュー・スレッドをGraphQLで取得
  - Copilot アカウント（`github-copilot` / `github-copilot[bot]`）のレビューが存在するか
  - Copilot が関与したスレッド（コメントを含む）がすべて `isResolved=true` であるか
- 未満の条件の場合、チェックを失敗させます（Required化でマージを停止）
  

## 必須化（Branch protection）
- `Copilot Review Gate / gate` を Required checks に追加してください。
- 例: `.github/branch-protection.main.verify-lite-noreview.json` に含めています。

## 使い方
- 通常のレビュー運用と同様に、Copilotにレビューを依頼（UIのCopilotレビュー機能）
- 指摘に対応し、PR上の「Resolve conversation」でスレッドを解決
- ワークフローが自動でグリーンになります
- 手動実行: Actions の `Copilot Review Gate` を `workflow_dispatch` で起動し、`pr_number` を指定（デフォルトブランチ以外の手動実行では必須）

### 補足: 既定のCopilotアクター
- 既定で検出するアクター: `copilot-pull-request-reviewer`, `github-copilot`, `github-copilot[bot]`, `copilot`, `copilot[bot]`
- もし組織内で別アカウント名の場合は、`.github/workflows/copilot-review-gate.yml` の `COPILOT_ACTORS` を編集してください。

## 例外運用
- Copilot が利用できない環境では、Requiredチェックに含めない運用、または `COPILOT_ACTORS` を空にして無効化できます（workflow の `env` を編集）。

## トラブルシューティング
- Copilotレビューが「コメント」のみで「レビュー」として表示されない場合は、Copilotレビューの起動方法を見直してください（PR画面のCopilotパネルからの実行を推奨）。
- スレッドが解決にならない場合、PR画面で各会話の「Resolve conversation」を押すか、対応コメントを行ってから解決してください。
- ゲートが検出しない場合、`COPILOT_ACTORS` の一覧に実際のアカウント名が含まれているか確認してください。
- fork PR では Actions がコメントを投稿できないため、ゲートはコメントを残さず `notice` のみ出力します（判定自体は実行されます）。
