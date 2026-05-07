# Security Assurance Lane cache-key fixture

この fixture は Issue #3266 の golden scenario です。小さな TypeScript 対象を使い、Security Assurance Lane の主要 artifact を外部 API / LLM / network なしで再生成します。

## 実行方法

```bash
pnpm run test:security-assurance
```

個別 runner を直接実行する場合:

```bash
node scripts/security/run-security-assurance-fixture.mjs --scenario cache-key
```

意図した artifact 変更を承認する場合は、差分をレビューしたうえで次を実行します。

```bash
node scripts/security/run-security-assurance-fixture.mjs --scenario cache-key --update-expected
```

## シナリオの読み方

- `SEC-CLAIM-001`: production `buildCacheKey` が `scope` を key material に含めないため、`security-findings.json` に candidate finding が出ます。`security-review.json` では `needs-human-review` に分類されます。
- `SEC-CLAIM-002`: token freshness check は response fixture で `no-finding` として扱います。
- `SEC-CLAIM-003`: `tests/fixtures/cache-helper.ts` は audit scope の `outOfScope` に該当するため、3-gate review で `out-of-scope` に分類されます。

## Artifact map

- `expected/security-claims.json`: `inputs/spec.md` から抽出された `security-claim/v1`。
- `expected/security-threat-model.json`: fixture 固定の `security-threat-model/v1`。
- `expected/security-code-map.json`: `inputs/target/src/**/*.ts` への deterministic pre-resolution map。
- `expected/security-audit-tasks.json`: proof-attempt task bundle。
- `expected/security-findings.json`: response fixture から生成された candidate findings。
- `expected/security-review.json`: Dead Code / Trust Boundary / Scope の 3-gate review 結果。
- `expected/assurance-summary.json`: security artifacts を assurance summary に接続した結果。
- `expected/claim-evidence-manifest.json`: security counts を含む claim-evidence manifest。
- `expected/security-summary.md`: golden scenario の人間向け要約。

runner は `generatedAt` と artifact path を正規化してから expected/actual を比較します。これにより、ローカルの worktree 名や一時 output directory 名による drift は検出対象外になります。
