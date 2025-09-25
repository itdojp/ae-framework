# Copilot Review Gate

目的: PR をマージする前に、GitHub Copilot によるコードレビューが存在し、その指摘（スレッド）が解決済みであることを必須化します。管理者/メンテナがPR作成者の場合は運用上の例外としてバイパスします。

## 仕組み
- Workflow: `.github/workflows/copilot-review-gate.yml`
- 動作: PRのレビュー一覧とレビュー・スレッドをGraphQLで取得
  - Copilot アカウント（`github-copilot` / `github-copilot[bot]`）のレビューが存在するか
  - Copilot が関与したスレッド（コメントを含む）がすべて `isResolved=true` であるか
- 未満の条件の場合、チェックを失敗させます（Required化でマージを停止）
 - 例外: PR作者がリポジトリの `admin` または `maintain` 権限を持つ場合、このゲートは早期成功（バイパス）します。

## 必須化（Branch protection）
- `Copilot Review Gate / gate` を Required checks に追加してください。
- 例: `.github/branch-protection.main.verify-lite-noreview.json` に含めています。

## 使い方
- 通常のレビュー運用と同様に、Copilotにレビューを依頼（UIのCopilotレビュー機能）
- 指摘に対応し、PR上の「Resolve conversation」でスレッドを解決
- ワークフローが自動でグリーンになります

## 例外運用
- Copilot が利用できない環境では、Requiredチェックに含めない運用、または `COPILOT_ACTORS` を空にして無効化できます（workflow の `env` を編集）。

## トラブルシューティング
- Copilotレビューが「コメント」のみで「レビュー」として表示されない場合は、Copilotレビューの起動方法を見直してください（PR画面のCopilotパネルからの実行を推奨）。
- スレッドが解決にならない場合、PR画面で各会話の「Resolve conversation」を押すか、対応コメントを行ってから解決してください。
