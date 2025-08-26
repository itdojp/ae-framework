# Contributing Guide

## How to Contribute
1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Submit a pull request

## Code Standards
- Follow existing code style
- Add tests for new features
- Update documentation

## Package Manager Policy (pnpm)

このリポジトリはパッケージマネージャとして pnpm を正とします。

- Node.js: 20.x 系を使用（`package.json#engines` 準拠）
- インストール: `pnpm install`
- 開発: `pnpm dev` など、スクリプトは `pnpm` で実行
- npm の lockfile 生成は無効化（`.npmrc` の `package-lock=false`）。`package-lock.json` はコミットしないでください。

pnpm の導入:

```bash
# 推奨: Corepack を使用
corepack enable
corepack prepare pnpm@latest --activate

# もしくはグローバルインストール
npm i -g pnpm
```

モノレポ構成のため、ワークスペースコマンドは `pnpm --filter` を活用してください（例: `pnpm --filter @ae-framework/ui build`）。
