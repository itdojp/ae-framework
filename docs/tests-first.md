# Tests-First Intent Mode

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

This guide describes the **tests-first** workflow proposed in #1067: generate tests immediately after intent capture, then **rank code candidates** by how well they satisfy those tests.

### Goals

- Make `ae tests:suggest` the default step after intent capture.
- Use `ae code:rank-by-tests` to select the best code candidate based on test outcomes.
- Provide starter prompts for common domains to reduce prompt variance.

### Workflow

1. **Intent**: Capture user requirements in natural language.
2. **Tests**: Generate tests that represent the intent.
3. **Candidates**: Produce multiple code candidates.
4. **Rank**: Run tests against each candidate and score them.
5. **Select**: Pick the top-ranked candidate and continue the pipeline.

### Ranking Heuristics (initial proposal)

```
score = pass_rate
      - flake_penalty
      - runtime_penalty

pass_rate       = passed_tests / total_tests
flake_penalty   = flake_count * 0.02
runtime_penalty = min(runtime_ms / 60000, 0.2)
```

Notes:
- Penalize flaky tests explicitly to avoid unstable selections.
- Cap runtime penalty to avoid over-penalizing complex suites.
- Adjust weights per project constraints (CI vs local).

### Templates

Starter prompts live in `templates/prompts/`:
- `templates/prompts/tests-first-http-api.md`
- `templates/prompts/tests-first-queue.md`
- `templates/prompts/tests-first-auth.md`
- `templates/prompts/tests-first-math.md`

Use these as baseline prompts for test generation to keep outputs consistent across runs.

### Next Steps

- Wire `ae tests:suggest` as the default route in the 6-phase docs and CLI.
- Implement `ae code:rank-by-tests` using the scoring heuristic above.
- Add optional `--autofix` flow to patch failing tests and re-rank.

---

## Japanese

本ドキュメントは、#1067 で提案する **tests-first** ワークフロー（Intent 直後にテスト生成し、テスト結果でコード候補を再ランク付けする方式）を整理します。

### 目的

- `ae tests:suggest` を Intent 直後の標準ステップにする。
- `ae code:rank-by-tests` でテスト結果に基づき最適候補を選ぶ。
- 代表ドメインのプロンプト雛形で出力のばらつきを抑える。

### ワークフロー

1. **Intent**: 要件を自然言語で取得。
2. **Tests**: Intent を表すテストを生成。
3. **Candidates**: 複数のコード候補を生成。
4. **Rank**: 候補ごとにテストを実行してスコア化。
5. **Select**: 最上位を採用し後続工程へ。

### ランキング指標（初期案）

```
score = pass_rate
      - flake_penalty
      - runtime_penalty

pass_rate       = passed_tests / total_tests
flake_penalty   = flake_count * 0.02
runtime_penalty = min(runtime_ms / 60000, 0.2)
```

注記:
- フレークは明示的に減点し、安定性を優先する。
- 実行時間ペナルティは上限を設け、複雑系の過剰減点を回避する。
- CI/ローカルなど制約に応じて重みを調整する。

### テンプレート

`templates/prompts/` 配下の雛形を利用:
- `templates/prompts/tests-first-http-api.md`
- `templates/prompts/tests-first-queue.md`
- `templates/prompts/tests-first-auth.md`
- `templates/prompts/tests-first-math.md`

テスト生成の基準プロンプトとして利用し、出力の一貫性を高めます。

### 次のステップ

- 6 相ドキュメントと CLI の既定を `ae tests:suggest` に更新。
- `ae code:rank-by-tests` を上記スコアリングで実装。
- 失敗テスト修正に向けた `--autofix` を追加。
