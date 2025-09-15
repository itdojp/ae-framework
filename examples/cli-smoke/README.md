# CLI Smoke Test

> 🌍 Language / 言語: English | 日本語

Minimal smoke tests to quickly verify that the runner boots and executes.

Two variants are provided:

- CJS + TypeScript (via `tsx` runtime)
  - Runs directly from TypeScript source without building.
  - Command: `node examples/cli-smoke/test-cli.cjs`

- ESM + JavaScript (from built artifacts)
  - Requires a build first.
  - Commands:
    - `pnpm build`
    - `node examples/cli-smoke/test-cli.mjs`

What it does:
- Invokes `main()` from the framework runner to perform a basic boot‑up and exit.
- Intended for quick sanity checks during development.

Notes:
- Ensure dependencies are installed: `pnpm install`
- If `test-cli.mjs` reports missing build artifacts, run `pnpm build` and retry.

---

## 日本語（概要）

ランナーが起動して最小限の処理を実行できるかを素早く確認するためのスモークテストです。

提供バリアント:

- CJS + TypeScript（`tsx` ランタイム）
  - TypeScript ソースから直接実行
  - コマンド: `node examples/cli-smoke/test-cli.cjs`

- ESM + JavaScript（ビルド済み成果物）
  - 事前にビルドが必要
  - コマンド: `pnpm build && node examples/cli-smoke/test-cli.mjs`

動作内容:
- フレームワークのランナー `main()` を呼び出し、基本起動→終了を確認

注意:
- 依存関係の導入: `pnpm install`
- `test-cli.mjs` でビルド成果物が見つからない場合は `pnpm build` を実行後に再試行
