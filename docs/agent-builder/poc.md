# Agent Builder PoC (最小手順)

## 目的
- #1053 PR-4 の最小PoC（Intent→Formal→Code→Verify）をローカルで再現できるようにする。
- 既存のサンプルフローと verify-lite サマリを使い、Envelope出力までを確認する。

## 前提
- `pnpm install` 済み
- Node.js 20+（`package.json` の engines に準拠）

## 実行

### 最小PoC（推奨）
```bash
npm run demo:ab-poc
```

### 直接実行
```bash
node scripts/agent-builder/flow-runner.mjs \
  --flow fixtures/flow/sample.flow.json \
  --summary packages/envelope/__fixtures__/verify-lite-summary.json \
  --output artifacts/agent-builder/envelope.json
```

## 出力
- `artifacts/agent-builder/envelope.json` に Envelope が生成される。

## 関連ファイル
- Flow 定義: `fixtures/flow/sample.flow.json`
- verify-lite サマリ: `packages/envelope/__fixtures__/verify-lite-summary.json`
- 実行スクリプト: `scripts/agent-builder/flow-runner.mjs`

## 注意
- 本PoCは最小のスタブ実行であり、実運用の検証フローとは異なる。
