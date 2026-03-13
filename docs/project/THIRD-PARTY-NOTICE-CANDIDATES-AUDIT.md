---
docRole: ssot
canonicalSource: docs/project/THIRD-PARTY-NOTICE-CANDIDATES-AUDIT.md
lastVerified: '2026-03-13'
owner: project-docs
verificationCommand: pnpm run license:audit:third-party -- --output-json artifacts/reference/legal/third-party-notice-candidate-audit.json --output-md artifacts/reference/legal/third-party-notice-candidate-audit.md
---

# Third-Party Notice Candidates Audit

## Purpose

`#2623` の Apache-2.0 切替判断に先立ち、tracked file と repo 構成から観測できる third-party / upstream / vendored notice candidate を deterministic に固定する。

この監査は legal conclusion ではなく、個別 notice 要否判断の factual input である。

## Outputs

- JSON: `artifacts/reference/legal/third-party-notice-candidate-audit.json`
- Markdown: `artifacts/reference/legal/third-party-notice-candidate-audit.md`

## What the audit checks

- nested `LICENSE` / `NOTICE` / `COPYING` 候補
- vendor-like path segment を持つ tracked path
- git submodule の有無

## Command

```bash
SOURCE_DATE_EPOCH=0 pnpm run license:audit:third-party --   --output-json artifacts/reference/legal/third-party-notice-candidate-audit.json   --output-md artifacts/reference/legal/third-party-notice-candidate-audit.md
```

## Interpretation

- `status=no-candidates`
  - tracked な nested legal file / vendored path / submodule は観測されなかった
  - `#2623` の「third-party / upstream サブツリーがある場合」の残件は、少なくとも repo 事実上は発火していない
- `status=review-required`
  - path 単位の候補が見つかっている
  - 個別 notice を root `NOTICE` / `THIRD_PARTY_NOTICES.md` / subtree notice にどう反映するかは人手判断が必要

## Current repository fact snapshot

2026-03-13 時点で `git ls-files` と `.gitmodules` を前提に確認した範囲では、repo root 以外の tracked legal file と tracked vendor-like subtree を deterministic に棚卸しできる状態になっている。
