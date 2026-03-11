---
docRole: narrative
lastVerified: '2026-03-11'
---
# P0: npx-first, scoped TDD guard, deterministic seed, bench+QA

> 🌍 Language / 言語: English | 日本語

## 🎯 目的（P0改修）

> 注記（現行実装）: この文書は P0 時点の historical proposal です。現行の canonical main CLI entrypoint は `src/cli/index.ts`、ベンチマーク専用CLIは `src/cli/benchmark-cli.ts` です。`src/cli.ts` / `src/runner/main.ts` は legacy compatibility shim として扱います。現行CLIの SSOT は `docs/reference/CLI-COMMANDS-REFERENCE.md` を参照してください。

- **npx ファースト運用**: グローバルインストール前提の排除
- **スコープ限定TDD ガード**: 対象範囲限定 + オプトアウト環境変数 + CI限定オプション
- **決定的実行**: 乱数シード（AE_SEED）による再現可能なベンチマーク
- **ベンチマーク**: tinybench + 環境情報付きJSONレポート生成
- **QA**: Jest coverage閾値強制（axe/lighthouse は雛形まで）
- **統一コマンド**: すべて `ae <domain>:<action>` として実行可能

## 📋 使い方

### 基本コマンド

```bash
# npx による実行（グローバルインストール不要）
npx ae-framework@latest ae --help
npx ae-framework@latest ae bench
npx ae-framework@latest ae tdd:guard
npx ae-framework@latest ae qa

# ローカルインストール後
npm install ae-framework
npx ae bench --seed 42
```

### 環境変数による制御

```bash
# TDDガードをスキップ
AE_SKIP_GUARD=1 npx ae tdd:guard

# 決定的ベンチマーク実行
AE_SEED=42 npx ae bench
```

### 設定ファイル (config/ae.config.ts)

```text
export default {
  mode: 'copilot', // 'copilot' | 'delegated'
  tddGuard: {
    enabled: true,
    onlyChanged: true,
    changedSince: 'origin/main',
    include: ['src/**/*.ts', 'tests/**/*.ts'],
    exclude: ['**/*.md'],
    allowSkipWithEnv: 'AE_SKIP_GUARD',
    ciOnly: false // CIでのみ実行する場合はtrue
  },
  qa: {
    coverageThreshold: {
      branches: 90, lines: 90, functions: 90, statements: 90
    }
  },
  bench: {
    warmupMs: 300,
    iterations: 30,
    seed: 12345
  }
};
```

補足: QA の coverage しきい値は `policy/quality.json` が単一情報源です。`config/ae.config.*` の `qa.coverageThreshold` はローカルヒント扱いで、CI では無視されます。
補足: `mode` はCLI挙動の既定値に影響します（copilot=自動修復はdry-run既定、delegated=修復後verify実行・統合テスト並列既定）。

## ✅ 検証結果

### 動作確認ログ

```bash
# CLI ヘルプ
$ npx ae --help
ae
Usage:
  $ ae <command> [options]
Commands:
  tdd:guard  Run TDD pre-commit guard
  bench      Run benchmarks  
  qa         Run QA metrics

# ベンチマーク実行
$ npx ae bench
[ae:bench] running with seed=12345, iterations=30, warmup=300ms
[ae:bench] artifacts generated -> artifacts/bench.{json,md}

# 決定的実行
$ AE_SEED=42 npx ae bench  
[ae:bench] running with seed=42, iterations=30, warmup=300ms
[ae:bench] artifacts generated -> artifacts/bench.{json,md}

# TDD ガード オプトアウト
$ AE_SKIP_GUARD=1 npx ae tdd:guard
[ae:tdd:guard] skipped by AE_SKIP_GUARD=1
```

### 生成されるベンチマークレポート例

```text
# Bench Report
- Date: 2025-08-24T22:34:25.405Z
- Node: v20.19.4
- Machine: linux/x64 AMD Ryzen 7 7735HS with Radeon Graphics
- Iter: 30, Warmup: 300ms, Seed: 42

| task | mean(ms) | stdev(ms) | hz |
|---|---:|---:|---:|
| noop | 0.044 | 1.353 | 26407537.5 |
```

## 🔧 互換性メモ

### パッケージマネージャ検出
- **npm**: package-lock.json 存在時
- **pnpm**: pnpm-lock.yaml 存在時  
- **yarn**: yarn.lock 存在時

### テストランナー検出
- **実行優先**: package.json scripts.test の内容を優先
- **依存関係フォールバック**: jest/vitest の依存関係を確認
- **vitest対応**: 通常テスト実行（coverage閾値は今後拡張予定）

### 環境対応
- **Node.js**: >=20.11 <23
- **モジュール**: ESM/CJS 両対応
- **TypeScript**: strict mode 準拠

## 🚪 回避方法（オプトアウト）

### TDD ガードを無効化
```bash
# 環境変数で一時的にスキップ
AE_SKIP_GUARD=1 git commit -m "message"

# 設定で恒久的に無効化
echo 'export default { tddGuard: { enabled: false } }' > config/ae.config.ts

# CIでのみ有効化
echo 'export default { tddGuard: { ciOnly: true } }' > config/ae.config.ts
```

### ファイルスコープ調整
```text
// config/ae.config.ts
export default {
  tddGuard: {
    include: ['src/**/*.ts'], // テスト対象を限定
    exclude: ['**/*.md', '**/*.json'], // 除外ファイル追加
    onlyChanged: false // 全ファイルを対象にする
  }
};
```

## 🔄 ロールバック方法

### package.json の復元
```bash
git checkout HEAD~1 -- package.json package-lock.json
npm install
```

### 新規ファイルの削除
```bash
rm -rf src/core src/runner src/commands/tdd src/commands/bench src/commands/qa
rm config/ae.config.ts src/cli.ts
```

### pre-commit フック削除（該当する場合）
```bash
# .husky/pre-commit から ae tdd:guard の行を削除
sed -i '/npx ae-framework.*ae tdd:guard/d' .husky/pre-commit
```

## 📊 実装内容

### 新規追加ファイル
- `src/cli/index.ts` - canonical なメインCLIエントリポイント
- `src/cli.ts` - legacy compatibility shim
- `src/core/config.ts` - zod設定スキーマ + 読み込み
- `src/core/seed.ts` - AE_SEED環境変数処理
- `src/runner/main.ts` - legacy `cac` compatibility router
- `src/commands/tdd/guard.ts` - スコープ限定TDDガード
- `src/commands/bench/run.ts` - tinybench + アーティファクト生成
- `src/commands/qa/run.ts` - カバレッジ閾値強制
- `config/ae.config.ts` - サンプル設定ファイル

### package.json 変更点
- `"ae": "./dist/cli.js"` bin エントリ追加
- `"engines": { "node": ">=20.11 <23" }` 更新
- 依存関係追加: execa, micromatch, tinybench, cac, @types/micromatch

## 🚦 次のステップ（P1/P2は別PR）

- [ ] vitest coverage閾値対応拡張
- [ ] axe/lighthouse QAコマンド実装
- [ ] Property-based testing統合
- [ ] ベンチマーク実処理タスク追加
- [ ] husky pre-commit 自動セットアップ

---

**作業時間**: 約2時間  
**コミット数**: 6個（段階的実装）  
**テスト**: 全新規コマンド動作確認済み
