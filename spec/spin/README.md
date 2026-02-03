# SPIN / Promela Specs

> 🌍 Language / 言語: English | 日本語

This directory contains Promela models for SPIN.

## Quickstart (local)

Prereqs:
- `spin`
- `gcc` (to compile `pan`)

Run the sample model:

```bash
pnpm run verify:spin -- --file spec/spin/sample.pml --ltl p_done
```

Artifacts:
- `artifacts/hermetic-reports/formal/spin-summary.json`

## Notes
- The runner is non-blocking by design (it always exits 0) and writes a summary JSON.
- In CI, the job is label-gated via `run-formal` (see `.github/workflows/formal-verify.yml`).

---

## 日本語（概要）

このフォルダには SPIN/Promela のモデル（`.pml`）を配置し、並行モデルの検査（デッドロック/安全性/ライブネス）をスモークテストとして実行できる状態にします。

### ローカル実行（例）

前提:
- `spin`
- `gcc`（SPIN が生成する `pan.c` のコンパイルに使用）

実行:
```bash
pnpm run verify:spin -- --file spec/spin/sample.pml --ltl p_done
```

成果物:
- `artifacts/hermetic-reports/formal/spin-summary.json`

補足:
- ランナーは **non-blocking**（常に exit 0）です。CI では主に「導線/成果物/集約表示」の確認を目的とします。
- CI 起動は PR ラベル `run-formal` で制御します（`.github/workflows/formal-verify.yml`）。
