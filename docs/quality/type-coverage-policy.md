---
docRole: derived
canonicalSource:
- policy/quality.json
- docs/quality/verification-gates.md
lastVerified: '2026-04-08'
---
# Type Coverage Policy (TSDoc)

> 🌍 Language / 言語: English | 日本語

---

## English

### Purpose
- Raise and enforce TypeScript type coverage incrementally without blocking fast iteration in the default path.

### Current baseline
- Current baseline: `65%`.
- Local baseline check: `pnpm typecov:check`.
- Incremental gate: `70%`, available via `pnpm typecov:check:70`.

### CI policy
- The stronger threshold is intended for label-gated enforcement in CI, for example behind `enforce-typecov`.
- Keep the default path lightweight; opt in to the stricter threshold when the change is ready for tighter type-quality enforcement.

### Local runs
- Quick local check: `pnpm types:check && pnpm typecov`
- Enforced check (`70%`): `pnpm typecov:check:70`

### Scope and exceptions
- Scope is defined by `configs/tsconfig/tsconfig.verify.json` and focuses on framework/core paths.
- Test scaffolding and examples are excluded from the coverage target.
- Catch blocks are ignored via `--ignore-catch`.
- Prefer narrowing over `any`.

### Error-handling rule
- Use unknown-first handling in `catch (error: unknown)`.
- Convert errors through a shared helper such as `toMessage(error)`.
- Do not rely on unsafe direct access like `error.message`.

### Escalation path
- If a PR cannot meet the raised threshold, remove the strict label.
- Leave a short note describing the hotspots and the follow-up work needed to close the gap.

## 日本語

### 目的
- 速度を落とさず、段階的に TypeScript の型カバレッジを引き上げ、必要時のみ強制ゲートを有効化します。

### 現在の基準
- 現在の基準: `65%`
- ローカル基準チェック: `pnpm typecov:check`
- 段階的ゲート: `70%`（`pnpm typecov:check:70`）

### CI ポリシー
- 強制しきい値は、たとえば `enforce-typecov` のようなラベル制御（label-gated）の CI でのみ有効化する前提です。
- 既定の開発経路は軽量のまま維持し、型品質を強めたい PR だけ厳格しきい値を選択します。

### ローカル実行
- クイック確認: `pnpm types:check && pnpm typecov`
- 強制チェック（`70%`）: `pnpm typecov:check:70`

### 対象範囲と例外
- 対象範囲は `configs/tsconfig/tsconfig.verify.json` で定義し、フレームワーク/コアを中心に計測します。
- テスト用の足場コードとサンプルは対象外です。
- `catch` 節は `--ignore-catch` で除外します。
- `any` ではなくナローイングを優先します。

### エラー処理ルール
- `catch (error: unknown)` を基本とします。
- 文字列化は `toMessage(error)` のような共通ヘルパを経由します。
- `error.message` の直接参照は避けます。

### エスカレーション
- PR で強制しきい値を満たせない場合は、ラベル `enforce-typecov` を外します。
- その上で、ホットスポットと後続対応を短く記録してください。
