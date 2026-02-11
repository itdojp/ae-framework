# Copilot Review Gate

目的: PR をマージする前に、GitHub Copilot によるコードレビューが存在し、その指摘（スレッド）が解決済みであることを必須化します。

## 仕組み
- Workflow: `.github/workflows/copilot-review-gate.yml`
- トリガー: `pull_request`, `pull_request_review`, `issue_comment`（auto-fix結果コメント更新時）, `workflow_dispatch`
- 動作: PRのレビュー一覧とレビュー・スレッドをGraphQLで取得
  - Copilot アカウント（`github-copilot` / `github-copilot[bot]`）のレビューが存在するか
  - Copilot が関与したスレッド（コメントを含む）がすべて `isResolved=true` であるか
- 未満の条件の場合、チェックを失敗させます（Required化でマージを停止）

関連:
- Copilot suggestion の自動適用（auto-fix）: `docs/ci/copilot-auto-fix.md`
- PR自動化の運用全体像（Copilot→auto-fix→auto-merge）: `docs/ci/pr-automation.md`
  

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

### 補足: wait/retry の調整（レビュー到着待ち）
- workflow 側 env の `COPILOT_REVIEW_WAIT_MINUTES` / `COPILOT_REVIEW_MAX_ATTEMPTS` を調整できます（既定: 5分 x 3回）。

## 例外運用
- Copilot が利用できない環境では、Requiredチェックに含めない運用、または `COPILOT_ACTORS` を空にして無効化できます（workflow の `env` を編集）。

## トラブルシューティング
- Copilotレビューが「コメント」のみで「レビュー」として表示されない場合は、Copilotレビューの起動方法を見直してください（PR画面のCopilotパネルからの実行を推奨）。
- スレッドが解決にならない場合、PR画面で各会話の「Resolve conversation」を押すか、対応コメントを行ってから解決してください。
- Copilot Auto Fix がスレッドを resolve しても、変更が push されない場合（既適用など）は、ゲートの再評価が走らないことがあります。Actions から `Copilot Review Gate` を再実行してください。
- ゲートが検出しない場合、`COPILOT_ACTORS` の一覧に実際のアカウント名が含まれているか確認してください。
- fork PR では Actions がコメントを投稿できないため、ゲートはコメントを残さず `notice` のみ出力します（判定自体は実行されます）。
- Required checks が `Expected — Waiting for status to be reported` のまま止まる場合は、branch protection に登録したチェック名が実際のジョブ名と一致しているか、PR条件でワークフローが実行されているかを確認してください。
  - 参考: docs/ci/branch-protection-operations.md の「Required checks が Pending のまま」セクション
