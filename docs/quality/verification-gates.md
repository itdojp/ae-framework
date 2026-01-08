# Verification Gates Guide

> 🌍 Language / 言語: English | 日本語

---

## English (summary)

Verification gates standardize **verify-then-merge**. This guide lists the available gate types, how to enable them, and where results are reported.

---

## 日本語（概要）

検証ゲートは **verify-then-merge** を実現するための基準です。本ドキュメントではゲート種別・有効化方法・レポート出力先を整理します。

## ゲート種別

- 基本ゲート: lint / types / coverage
- 追加ゲート: property / contract / mutation / MBT / perf / a11y / lighthouse
- Formal: TLA+ / Alloy / conformance (report-only → opt-in)

## 有効化の指針（既存運用のまとめ）

- PRデフォルトは軽量ゲート（Verify Lite）
- 重いゲートは **ラベルで opt-in** する
- しきい値系（perf/lh/a11y）は `enforce-*` ラベルでブロッキング化

関連ドキュメント:
- `docs/ci/label-gating.md`
- `docs/ci/stable-profile.md`
- `docs/quality/adapter-thresholds.md`

## 代表的なゲートと入口

| Gate | How to enable | Primary output | Notes |
| --- | --- | --- | --- |
| property | label `run-property` | `artifacts/properties/` | CI Extended 側で実行 |
| contract | `pnpm pipelines:pact` | `artifacts/contracts/` | API契約の検証 |
| mutation | label `run-mutation` | `reports/mutation/` | quick mode + ignoreStatic |
| MBT | label `run-mbt` | `artifacts/mbt/` | CI Extended 側 |
| perf/a11y/lh | label `enforce-perf` / `enforce-a11y` / `enforce-lh` | `reports/*.json` | しきい値でブロッキング |

## PRレポート

- 既存テンプレ: `docs/quality/pr-summary-template.md`
- 仕様: `docs/quality/pr-summary-tool.md`
- 目的: 検証結果を PR に要約して**人間が判断**できる形にする

## 注意（machine verifying machine）

- AIがコードとテストを同時に生成すると盲点が共有される
- Spec Kit / Blueprint に **対抗的なテスト設計** を明記し、人間が責任を持つ
- verify-then-merge は「**CI合格 + 人間承認**」が基本
