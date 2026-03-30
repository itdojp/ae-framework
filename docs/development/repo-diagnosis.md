---
docRole: ssot
lastVerified: '2026-03-31'
owner: development-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Repository Diagnosis Report

> 🌍 Language / 言語: English | 日本語

---

## English

### Overview
This report captures a point-in-time diagnosis of the current repository baseline. The values below were verified against the local workspace on 2026-03-31 and should be refreshed when the package manager, CLI surface, or build layout changes.

### Environment detection
| Item | Current state |
| --- | --- |
| Node.js | `v22.0.0` |
| Package manager baseline | `pnpm` (`pnpm-lock.yaml` present, `package-lock.json` absent) |
| Module type | ESM (`"type": "module"`) |
| Test runner | Vitest present in the current toolchain |
| Build system | TypeScript via `tsc` |

### Dependency status
The dependencies that were previously tracked as missing for early P0 implementation are now present.

| Dependency | Status |
| --- | --- |
| `zod` | present |
| `execa` | present |
| `micromatch` | present |
| `tinybench` | present |
| `cac` | present |

### Directory structure
- `src/` exists
- `src/cli/` exists
- `dist/` exists as the build output surface

### Current CLI bin inventory
Current `package.json#bin` entries:
- `ae`
- `ae-framework`
- `ae-phase`
- `ae-approve`
- `ae-slash`
- `ae-ui`
- `ae-sbom`
- `ae-resilience`
- `ae-benchmark`
- `ae-server`

### Diagnosis summary
The earlier repository diagnosis that identified missing dependencies is no longer current. The baseline has moved from dependency bootstrap work to surface consistency and operational hygiene.

Current takeaways:
1. the repository is aligned to `pnpm`, not `npm`
2. the primary CLI surface already includes both `ae` and `ae-framework`
3. the previously missing P0 dependency set is already installed
4. future diagnosis updates should focus on command-surface drift, docs freshness, and build/runtime consistency rather than dependency bootstrap gaps

### Operating notes
- treat this document as a snapshot report, not a permanent roadmap
- when CLI bins, lockfiles, or build directories change, update this report together with the affected operational docs
- if a future diagnosis needs remediation planning, record that plan separately instead of mixing it into this snapshot

## 日本語

### 概要
本レポートは、current repository baseline の point-in-time diagnosis を記録するものです。以下の値は 2026-03-31 時点の local workspace に対して確認したものであり、package manager、CLI surface、build layout が変わった場合は更新が必要です。

### 環境検出
| 項目 | 現在の状態 |
| --- | --- |
| Node.js | `v22.0.0` |
| package manager baseline | `pnpm`（`pnpm-lock.yaml` が存在し、`package-lock.json` は存在しない） |
| module type | ESM（`"type": "module"`） |
| test runner | current toolchain に Vitest が含まれる |
| build system | `tsc` による TypeScript build |

### dependency 状態
初期の P0 実装で「不足」として扱っていた dependency は、現在はすべて存在します。

| dependency | 状態 |
| --- | --- |
| `zod` | present |
| `execa` | present |
| `micromatch` | present |
| `tinybench` | present |
| `cac` | present |

### directory structure
- `src/` は存在する
- `src/cli/` は存在する
- `dist/` は build output surface として存在する

### current CLI bin inventory
現在の `package.json#bin` entry:
- `ae`
- `ae-framework`
- `ae-phase`
- `ae-approve`
- `ae-slash`
- `ae-ui`
- `ae-sbom`
- `ae-resilience`
- `ae-benchmark`
- `ae-server`

### diagnosis summary
不足 dependency を前提とした earlier repository diagnosis は、現在の baseline には一致しません。現在の関心は dependency bootstrap ではなく、surface consistency と operational hygiene です。

現在の要点:
1. repository は `npm` ではなく `pnpm` baseline に揃っている
2. primary CLI surface には `ae` と `ae-framework` の両方が存在する
3. 以前不足していた P0 dependency 群はすでに導入済みである
4. 今後の diagnosis 更新は dependency bootstrap gap ではなく、command-surface drift、docs freshness、build/runtime consistency を中心に扱うべきである

### 運用メモ
- 本書は permanent roadmap ではなく snapshot report として扱う
- CLI bin、lockfile、build directory が変わる場合は、関連する operational doc と同時に更新する
- remediation plan が必要になった場合は、この snapshot に混在させず別文書として管理する
