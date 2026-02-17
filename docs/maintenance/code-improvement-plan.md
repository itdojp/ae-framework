# Code Improvement Plan (Issue #2031 / Phase 0)

最終更新: 2026-02-17

## 1. 目的

ソースコード改善は、次の3点を同時に達成することを目的とする。

- 型安全性の向上（`any` 依存の削減）
- 保守性の向上（巨大ファイルの責務分割）
- 変更時の回帰リスク低減（テスト補強・エラー契約統一）

## 2. ベースライン（2026-02-17）

- `src` 内 `any` 使用数（単純集計）: **1166**
- `TODO/FIXME`（`src/scripts/tests/docs`）: **141**
- 1000行超 TSファイル（抜粋）:
  - `src/agents/code-generation-agent.ts` (1377行)
  - `src/cli/conformance-cli.ts` (1374行)
  - `src/agents/intent-agent.ts` (1343行)
  - `src/utils/enhanced-state-manager.ts` (1296行)
  - `src/agents/validation-task-adapter.ts` (1266行)

## 3. 優先順位付けルール

優先度 = `影響度 × 変更頻度 × 型負債密度 ÷ 分割容易性`

評価観点:
- 影響度: CLI入口、CI利用、外部公開APIに近いか
- 変更頻度: 直近PRで変更が多いか
- 型負債密度: `any` / 型アサーションの多さ
- 分割容易性: 依存が密でないか（循環参照リスク）

## 4. 先行対象（Phase 2の初手）

### 4.1 型負債先行（`any` 上位）

1. `src/agents/domain-modeling-task-adapter.ts`
2. `src/inference/core/solution-composer.ts`
3. `src/agents/validation-task-adapter.ts`
4. `src/services/container/docker-engine.ts`
5. `src/services/container/podman-engine.ts`

### 4.2 分割先行（巨大ファイル）

1. `src/cli/conformance-cli.ts`
2. `src/agents/code-generation-agent.ts`
3. `src/agents/intent-agent.ts`
4. `src/utils/enhanced-state-manager.ts`

## 5. 実装ルール

1. **1 PR = 1ファイル主対象**  
   分割対象を複数ファイル同時に触らない。
2. **境界から型を入れる**  
   I/O境界（CLI引数、JSON、外部コマンド結果）に Zod/明示型を先に追加。
3. **戻り値契約を先に固定**  
   `Result` 形式・exit code・エラーメッセージをテストで固定してから内部実装を変える。
4. **無名TODOを残さない**  
   `TODO(#issue): ...` 形式でIssue参照を必須化。

## 6. TODO（実装向け）

### Phase 2-A: 型安全性
- [ ] `src/agents/domain-modeling-task-adapter.ts` の `any` 削減（PR1）
- [ ] `src/inference/core/solution-composer.ts` の `any` 削減（PR2）
- [ ] `src/agents/validation-task-adapter.ts` の `any` 削減（PR3）
- [ ] container engine 2ファイルの共通型抽出（PR4）
- [ ] `pnpm -s run types:check` をPRごとに通過させる

### Phase 2-B: 責務分割
- [ ] `src/cli/conformance-cli.ts` を `parser` / `executor` / `formatter` に分割
- [ ] `src/agents/code-generation-agent.ts` を `planning` / `generation` / `validation` へ分離
- [ ] `src/agents/intent-agent.ts` の推論・I/Oを分離
- [ ] `src/utils/enhanced-state-manager.ts` の永続化層を独立モジュール化
- [ ] 分割ごとに回帰テストを追加

### Phase 2-C: 規約統一
- [ ] エラーコード規約を主要CLIに適用
- [ ] ログ形式（prefix/phase/duration）を統一
- [ ] TODO/FIXME を Issue参照付きへ更新

## 7. 受け入れ条件（コード改善）

- 先行5ファイルで `any` を段階的に削減できている
- 1000行超ファイルを少なくとも2本分割し、責務が分離されている
- 主要CLI/runnerのエラー契約がテストで固定されている
- 改善PR群がCI必須ゲートを継続通過している

## 8. トラッキング方法

- 各PRに「対象ファイル」「削減した `any` 件数」「追加テスト」を明記
- Issue #2031 のチェックリストをPRマージ後に更新
- 最終的に `before/after` の差分メトリクスをIssueコメントに集約
