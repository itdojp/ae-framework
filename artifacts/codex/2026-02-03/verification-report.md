# 旧版 ae-framework 形式検査ツール実行レポート (2026-02-03)

## 対象
- リポジトリ: /home/devuser/work/CodeX/ae-framework_exp01/ae-framework
- 旧版: v1.0.0 (14b3a49d9203eb7b1844802ccd6c7e9cab74a7fd)
  - 利用可能なタグが v1.0.0 のみのため、本タグを旧版として選定
- ブランチ: chore/ci-formal-old-20260203

## 環境
- Node: v22.19.0
- pnpm: 10.17.1
- Java: 17.0.16

## 実行コマンド一覧と結果

| 手順 | コマンド | 結果 |
| --- | --- | --- |
| 2 | pnpm install --frozen-lockfile \|\| pnpm install --no-frozen-lockfile | 失敗（依存解決） |
| 3 | pnpm run verify:conformance | 未対応（スクリプト欠損） |
| 3 | pnpm run trace:validate | 未対応（スクリプト欠損） |
| 4 | pnpm run verify:tla -- --engine=tlc | 未対応（スクリプト欠損） |
| 5 | pnpm run verify:smt -- --solver=z3 --file spec/smt/sample.smt2 | 未対応（スクリプト欠損） |
| 6 | Alloy jar 取得 | 成功（.cache/tools/alloy.jar） |
| 6 | pnpm run verify:alloy -- --file spec/alloy/Domain.als | 未対応（スクリプト欠損） |
| 7 | node scripts/formal/verify-apalache.mjs --file spec/tla/DomainSpec.tla | 失敗（スクリプト欠損） |
| 8 | node scripts/formal/verify-kani.mjs | 失敗（スクリプト欠損） |
| 9 | pnpm run verify:model | 未対応（スクリプト欠損） |
| 10 | pnpm run verify:formal | 未対応（スクリプト欠損） |

### 成功/失敗/スキップ内訳
- 成功: 1（Alloy jar 取得）
- 失敗: 3（pnpm install / Apalache / Kani）
- スキップ（未対応）: 7（verify:* / trace:* スクリプト欠損）

## 失敗ログ断片（先頭/末尾）と原因候補

### 依存導入
- ログ: artifacts/codex/2026-02-03/pnpm-install.log
- 先頭/末尾（同一ログ内）
```
ERR_PNPM_NO_LOCKFILE Cannot install with "frozen-lockfile" because pnpm-lock.yaml is absent
...
ERR_PNPM_NO_MATCHING_VERSION No matching version found for fastify-openapi-glue@^5.5.0
```
- 原因候補: 旧版の依存指定が npm レジストリの現行公開バージョンと不整合。

### Apalache
- ログ: artifacts/codex/2026-02-03/verify-apalache.log
- 先頭/末尾
```
Error: Cannot find module /home/devuser/work/CodeX/ae-framework_exp01/ae-framework/scripts/formal/verify-apalache.mjs
Node.js v22.19.0
```
- 原因候補: 旧版に Apalache 検証スクリプトが未導入。

### Kani
- ログ: artifacts/codex/2026-02-03/verify-kani.log
- 先頭/末尾
```
Error: Cannot find module /home/devuser/work/CodeX/ae-framework_exp01/ae-framework/scripts/formal/verify-kani.mjs
Node.js v22.19.0
```
- 原因候補: 旧版に Kani 検証スクリプトが未導入。

## 欠損ファイル確認
- artifacts/codex/2026-02-03/file-checks.txt
- 欠損: spec/smt/sample.smt2, spec/alloy/Domain.als, spec/tla/DomainSpec.tla, scripts/formal/verify-apalache.mjs, scripts/formal/verify-kani.mjs

## 生成成果物
- artifacts/codex/2026-02-03/ (各ログ/環境/状態記録)
- .cache/tools/alloy.jar

## まとめ
- 旧版 v1.0.0 では、形式検査ツール群のスクリプト/サンプルが未導入のため、大半が未対応。
- 依存導入もレジストリのバージョン不整合で失敗。
- 形式検査ツール群の動作検証を行うには、更新版（最新 main 以降）への切替が必要。
