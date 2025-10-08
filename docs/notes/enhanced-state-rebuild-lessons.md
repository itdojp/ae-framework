# EnhancedStateManager 再構築で得たナレッジ

## ブランチ運用
- `main` 取り込みは 1 日 1 回を目安に行い、履歴乖離を 1 リリース未満に抑える。
- 大きな分岐は機能ブロックごとに細分化し、Copilot 対応など一時的な変更は既存ブランチに積まず `--force-with-lease` で正規ブランチを維持する。

## テストの粒度
- `scripts/mutation/run-scoped.sh --quick` を差分 `STRYKER_CONFIG` 指定で走らせ、Stryker サンドボックスの警告を早期検知する。
- プロパティテストは再現性の高いシード設定 (`FC_SEED`) を記録し、 circuit breaker / token optimizer の失敗は即座に緩和ガードを追加する。

## 手戻り防止
- バッチスクリプトや docs の変更は専用 note に記録し、後続タスクで引用可能な URL（PR / commit）を併記する。
- 大規模再適用時は diff-scope 用のリストを先に作り、適用順序と確認テストを issue チェックリストにひも付ける。

参考: PR #1090 / ブランチ `feature/1084-stryker-quick-run-stabilize`
