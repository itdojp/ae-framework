# Lean4 Specs

> 🌍 Language / 言語: English | 日本語

This directory contains Lean4 proofs used as a lightweight, CI-friendly verification layer.

## Quickstart (local)

Prereqs:
- `elan` (Lean toolchain installer)
- `lake` (installed via the Lean toolchain)

Install `elan`:

```bash
curl -L -sS https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

Build (runs `lake build` under `spec/lean/`):

```bash
pnpm run verify:lean
```

Artifacts:
- `artifacts/hermetic-reports/formal/lean-summary.json`

## Notes
- The toolchain is pinned via `spec/lean/lean-toolchain`.
- The CI job installs `elan`, restores caches, and runs `lake build` (see `.github/workflows/formal-verify.yml`).

---

## 日本語（概要）

このフォルダには Lean4 の証明（型検査）を配置し、モデル検査とは補完関係にある「一般性のある性質」を CI でスモークテストできる状態にします。

### ローカル実行（例）

前提:
- `elan`（Lean toolchain インストーラ）
- `lake`（Lean toolchain に含まれるビルドツール）

`elan` を導入:

```bash
curl -L -sS https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

ビルド（`spec/lean/` で `lake build` を実行）:

```bash
pnpm run verify:lean
```

成果物:
- `artifacts/hermetic-reports/formal/lean-summary.json`

補足:
- Lean のバージョンは `spec/lean/lean-toolchain` で固定しています。
- CI では `elan` を導入し、キャッシュを復元した上で `lake build` を実行します（`.github/workflows/formal-verify.yml`）。
