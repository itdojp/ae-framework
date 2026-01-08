# Issue #1006: Script Inventory (2026-01-07)

## 概要
- 対象: `package.json` の `scripts`
- 集計方法: `:` の前半プレフィックスで分類（例: `test:ci` → `test`）
- 総数: 311

## プレフィックス別の件数
| prefix | count | share |
| --- | ---: | ---: |
| test | 69 | 22.2% |
| (root) | 22 | 7.1% |
| quality | 15 | 4.8% |
| codex | 13 | 4.2% |
| verify | 13 | 4.2% |
| flake | 12 | 3.9% |
| security | 12 | 3.9% |
| spec | 10 | 3.2% |
| state | 8 | 2.6% |
| benchmark | 7 | 2.3% |
| build | 7 | 2.3% |
| circuit-breaker | 7 | 2.3% |
| codegen | 7 | 2.3% |
| api | 6 | 1.9% |
| pipelines | 6 | 1.9% |
| hermetic | 5 | 1.6% |
| optimize | 5 | 1.6% |
| release | 5 | 1.6% |
| accessibility | 4 | 1.3% |
| clean | 4 | 1.3% |
| failures | 4 | 1.3% |
| ir | 4 | 1.3% |
| lint | 4 | 1.3% |
| mcp | 4 | 1.3% |
| package | 4 | 1.3% |
| conformance | 3 | 1.0% |
| container | 3 | 1.0% |
| dev | 3 | 1.0% |
| perf | 3 | 1.0% |
| validate | 3 | 1.0% |
| agent | 2 | 0.6% |
| bdd | 2 | 0.6% |
| codemod | 2 | 0.6% |
| operate | 2 | 0.6% |
| trace | 2 | 0.6% |
| typecov | 2 | 0.6% |
| agents | 1 | 0.3% |
| analyze | 1 | 0.3% |
| artifacts | 1 | 0.3% |
| demo | 1 | 0.3% |
| dependency | 1 | 0.3% |
| e2e | 1 | 0.3% |
| flow | 1 | 0.3% |
| formal | 1 | 0.3% |
| formal-agent | 1 | 0.3% |
| generate | 1 | 0.3% |
| hooks | 1 | 0.3% |
| intent-agent | 1 | 0.3% |
| monitoring | 1 | 0.3% |
| mutation | 1 | 0.3% |
| optimization | 1 | 0.3% |
| parallel | 1 | 0.3% |
| performance | 1 | 0.3% |
| playwright | 1 | 0.3% |
| podman | 1 | 0.3% |
| pretest | 1 | 0.3% |
| setup-hooks | 1 | 0.3% |
| smart-test | 1 | 0.3% |
| start | 1 | 0.3% |
| tools | 1 | 0.3% |
| type-check | 1 | 0.3% |
| types | 1 | 0.3% |
| visual | 1 | 0.3% |

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

## 再生成
```bash
node scripts/admin/generate-script-inventory.mjs docs/notes/issue-1006-script-inventory.md
```

## メモ
- `test`/`quality`/`verify`/`flake`/`security` で過半を占めるため、Phase 1 の統合対象候補。
- `(root)` は移行後にカテゴリへ再配置する前提で精査が必要。
