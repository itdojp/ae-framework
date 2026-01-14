# Type Coverage Policy (TSDoc)

> 🌍 Language / 言語: English | 日本語

English

- Target: Raise and enforce TypeScript type coverage over time without blocking fast iteration.
- Current baseline: 65% (script: `pnpm typecov:check`).
- Incremental gate: 70% available via `pnpm typecov:check:70`; wire this in CI behind a label (e.g., `enforce-typecov`).
- Local runs:
  - Quick check: `pnpm types:check && pnpm typecov`
  - Enforced check (70%): `pnpm typecov:check:70`
- Scope: Uses `configs/tsconfig/tsconfig.verify.json` to focus on framework/core paths; test scaffolding and examples are excluded.
- Exceptions: Catch blocks are ignored (`--ignore-catch`). Prefer narrowing, not `any`.
- Error handling: Use unknown-first in `catch (error: unknown)` and convert via a shared helper (e.g., `toMessage(error)`), avoiding unsafe `error.message` access.
- Escalation path: If a PR cannot meet the raised threshold, remove the label and leave a short note explaining hotspots and follow-ups.

Japanese (日本語)

- 目的: 速度を落とさず、段階的に TypeScript の型カバレッジを引き上げ、最終的に CI でのゲートを強化します。
- 現在の基準: 65%（`pnpm typecov:check`）。
- 段階的ゲート: 70% は `pnpm typecov:check:70` で実行可能。CI 側では `enforce-typecov` ラベルが付与された場合にのみ実行・強制します。
- ローカル実行:
  - 迅速な確認: `pnpm types:check && pnpm typecov`
  - 強制チェック（70%）: `pnpm typecov:check:70`
- 対象範囲: `configs/tsconfig/tsconfig.verify.json` を使用し、フレームワーク/コアを中心に計測。テスト・サンプルは除外。
- 例外: `catch` 節は `--ignore-catch` で除外。`any` ではなくナローイングを推奨。
- エラー処理: `catch (error: unknown)` を基本とし、共通ヘルパ（例: `toMessage(error)`）で安全に文字列化。`error.message` の直接参照は避ける。
- エスカレーション: PR で閾値を満たせない場合はラベルを外し、ホットスポットと後続対応を簡潔に記載してください。
