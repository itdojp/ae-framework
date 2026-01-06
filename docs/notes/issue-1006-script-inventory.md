# Issue #1006: Script Inventory (2026-01-06)

## 概要
- 対象: `package.json` の `scripts`
- 集計方法: `:` の前半プレフィックスで分類（例: `test:ci` → `test`）
- 総数: 311

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
| benchmark | 7 |
| build | 7 |
| circuit-breaker | 7 |
| codegen | 7 |
| api | 6 |
| pipelines | 6 |
| hermetic | 5 |
| optimize | 5 |
| release | 5 |
| accessibility | 4 |
| clean | 4 |
| failures | 4 |
| ir | 4 |
| lint | 4 |
| mcp | 4 |
| package | 4 |
| conformance | 3 |
| container | 3 |
| dev | 3 |
| perf | 3 |
| validate | 3 |
| agent | 2 |
| bdd | 2 |
| codemod | 2 |
| operate | 2 |
| trace | 2 |
| typecov | 2 |
| agents | 1 |
| analyze | 1 |
| artifacts | 1 |
| demo | 1 |
| dependency | 1 |
| e2e | 1 |
| flow | 1 |
| formal | 1 |
| formal-agent | 1 |
| generate | 1 |
| hooks | 1 |
| intent-agent | 1 |
| monitoring | 1 |
| mutation | 1 |
| optimization | 1 |
| parallel | 1 |
| performance | 1 |
| playwright | 1 |
| podman | 1 |
| pretest | 1 |
| setup-hooks | 1 |
| smart-test | 1 |
| start | 1 |
| tools | 1 |
| type-check | 1 |
| types | 1 |
| visual | 1 |

## (root) scripts 一覧
- ae-framework
- bdd
- benchmark
- build
- contract
- coverage
- dev
- formal-agent
- formal-spec
- generate-tla
- intent-agent
- lint
- mbt
- model-check
- mutation
- pbt
- phase
- setup-hooks
- test
- typecov
- validate-specs
- validate-tdd

## メモ
- `test`/`quality`/`verify`/`flake`/`security` で過半を占めるため、Phase 1 の統合対象候補。
- `(root)` は移行後にカテゴリへ再配置する前提で精査が必要。
