# Issue #1006: Script Inventory (2026-01-02)

## 概要
- 対象: `package.json` の `scripts`
- 集計方法: `:` の前半プレフィックスで分類（例: `test:ci` → `test`）
- 総数: 309

## プレフィックス別の件数
| prefix | count |
| --- | ---: |
| test | 69 |
| (root) | 22 |
| quality | 15 |
| codex | 13 |
| verify | 13 |
| flake | 12 |
| security | 12 |
| spec | 10 |
| state | 8 |
| build | 7 |
| benchmark | 7 |
| codegen | 7 |
| circuit-breaker | 7 |
| api | 6 |
| pipelines | 6 |
| optimize | 5 |
| hermetic | 5 |
| release | 5 |
| lint | 4 |
| clean | 4 |
| ir | 4 |
| package | 4 |
| accessibility | 4 |
| failures | 4 |
| mcp | 4 |
| dev | 3 |
| perf | 3 |
| container | 3 |
| validate | 3 |
| conformance | 3 |
| codemod | 2 |
| typecov | 2 |
| agent | 2 |
| operate | 2 |
| trace | 2 |
| bdd | 2 |
| start | 1 |
| types | 1 |
| type-check | 1 |
| pretest | 1 |
| setup-hooks | 1 |
| intent-agent | 1 |
| agents | 1 |
| formal-agent | 1 |
| playwright | 1 |
| e2e | 1 |
| visual | 1 |
| smart-test | 1 |
| parallel | 1 |
| monitoring | 1 |
| optimization | 1 |
| analyze | 1 |
| dependency | 1 |
| performance | 1 |
| hooks | 1 |
| formal | 1 |
| tools | 1 |
| artifacts | 1 |
| generate | 1 |
| podman | 1 |
| mutation | 1 |

## メモ
- `test`/`quality`/`verify`/`flake`/`security` で過半を占めるため、Phase 1 の統合対象候補。
- `(root)` は移行後にカテゴリへ再配置する前提で精査が必要。
