---
docRole: ssot
canonicalSource: docs/project/CONDITIONAL-ASSET-PROVENANCE-AUDIT.md
lastVerified: "2026-03-13"
owner: project-docs
verificationCommand: pnpm run license:audit:conditional -- --output-json artifacts/reference/legal/conditional-asset-audit.json --output-md artifacts/reference/legal/conditional-asset-audit.md
---

# Conditional Asset Provenance Audit

## 目的

`artifacts/**`, `fixtures/**`, `test-cassettes/**` は first-party 固定ではないため、Apache-2.0 切替判断の前に path ベースの provenance inventory を固定する。

この文書は legal conclusion ではなく、review 入力を deterministic に生成するための運用文書である。

## コマンド

```bash
pnpm run license:audit:conditional -- \
  --output-json artifacts/reference/legal/conditional-asset-audit.json \
  --output-md artifacts/reference/legal/conditional-asset-audit.md
```

`SOURCE_DATE_EPOCH=<unix-seconds>` を指定すると、`generatedAt` を固定して再現可能な snapshot を得る。出力 JSON / Markdown には `gitHeadSha` も含まれ、後続の legal audit と同一 head で生成したかを比較できる。

## 出力

- `artifacts/reference/legal/conditional-asset-audit.json`
- `artifacts/reference/legal/conditional-asset-audit.md`

## origin class

- `tracked-reference-snapshot`
- `tracked-archive`
- `local-debug-archive`
- `committed-contract-artifact`
- `runtime-output-or-unclassified`
- `test-fixture`
- `test-cassette`

## 解釈

- `tracked-reference-snapshot` / `tracked-archive` は tracked な reference 系 snapshot として扱う
- `committed-contract-artifact` は repo が契約物として commit している artifact であり、由来確認は別途必要
- `runtime-output-or-unclassified` は path だけでは provenance を断定できない
- `test-fixture` / `test-cassette` は test input であり、外部由来が混在しうる

## 関連文書

- `docs/project/LICENSE-MIGRATION-AUDIT.md`
- `LICENSE-SCOPE.md`
- `THIRD_PARTY_NOTICES.md`
