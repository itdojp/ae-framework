# Automation Rollback Validation Report (2026-02-14)

`scripts/ci/automation-rollback.sh` の dry-run 検証結果を記録する。

## 前提

- 実行日: 2026-02-14
- 対象リポジトリ: `itdojp/ae-framework`
- 実行リビジョン: `1907d078`（`main`）
- 実行環境:
  - `gh version 2.45.0 (2025-07-18 Ubuntu 2.45.0-1ubuntu0.3)`
  - `GNU bash, version 5.2.21(1)-release`

## 検証観点

1. スクリプト構文が正常（`bash -n`）
2. `merge` / `write` / `freeze` / `unfreeze` が dry-run で意図した変数更新を出力する
3. `status` が現行 Variables を読み出せる

## 実行コマンド

```bash
bash -n scripts/ci/automation-rollback.sh
AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh merge
AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh write
AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh freeze
AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh unfreeze
GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh status
```

## 実行結果（時系列ログ）

```text
# validation started 2026-02-14T15:11:04+09:00
$ date -Iseconds
2026-02-14T15:11:04+09:00
$ bash -n scripts/ci/automation-rollback.sh
$ date -Iseconds
2026-02-14T15:11:04+09:00
$ AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh merge
[dry-run] gh variable set AE_AUTO_MERGE --repo itdojp/ae-framework --body 0
[dry-run] gh variable set AE_CODEX_AUTOPILOT_ENABLED --repo itdojp/ae-framework --body 0
$ date -Iseconds
2026-02-14T15:11:04+09:00
$ AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh write
[dry-run] gh variable set AE_AUTOMATION_GLOBAL_DISABLE --repo itdojp/ae-framework --body 1
$ date -Iseconds
2026-02-14T15:11:04+09:00
$ AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh freeze
[dry-run] gh variable set AE_AUTO_MERGE --repo itdojp/ae-framework --body 0
[dry-run] gh variable set AE_CODEX_AUTOPILOT_ENABLED --repo itdojp/ae-framework --body 0
[dry-run] gh variable set AE_COPILOT_AUTO_FIX --repo itdojp/ae-framework --body 0
[dry-run] gh variable set AE_SELF_HEAL_ENABLED --repo itdojp/ae-framework --body 0
[dry-run] gh variable set AE_AUTOMATION_GLOBAL_DISABLE --repo itdojp/ae-framework --body 1
$ date -Iseconds
2026-02-14T15:11:04+09:00
$ AE_ROLLBACK_DRY_RUN=1 GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh unfreeze
[dry-run] gh variable set AE_AUTOMATION_GLOBAL_DISABLE --repo itdojp/ae-framework --body 0
$ date -Iseconds
2026-02-14T15:11:04+09:00
$ GH_REPO=itdojp/ae-framework scripts/ci/automation-rollback.sh status
# repo: itdojp/ae-framework
AE_AUTOMATION_GLOBAL_DISABLE=<unset>
AE_AUTO_MERGE=<unset>
AE_CODEX_AUTOPILOT_ENABLED=<unset>
AE_COPILOT_AUTO_FIX=<unset>
AE_SELF_HEAL_ENABLED=<unset>
# validation finished 2026-02-14T15:11:04+09:00
```

## 判定

- 構文チェック: 合格
- dry-run:
  - `merge`: `AE_AUTO_MERGE`, `AE_CODEX_AUTOPILOT_ENABLED` を更新予定として出力
  - `write`: `AE_AUTOMATION_GLOBAL_DISABLE=1` を更新予定として出力
  - `freeze`: `merge` + `AE_COPILOT_AUTO_FIX`, `AE_SELF_HEAL_ENABLED`, `AE_AUTOMATION_GLOBAL_DISABLE` を更新予定として出力
  - `unfreeze`: `AE_AUTOMATION_GLOBAL_DISABLE=0` を更新予定として出力
- `status`: Variables 読み出しが正常（この実行時点ではすべて `<unset>`）

## 備考

- 本検証は dry-run であり、Repository Variables の実値は変更していない。
- 実運用で停止する場合は `AE_ROLLBACK_DRY_RUN` を付けずに実行する。

