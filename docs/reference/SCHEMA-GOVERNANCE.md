# Schema Governance (`$id` canonical URI policy)

> Language / 言語: English | 日本語

---

## English

This document defines URI governance for JSON Schema identifiers in `schema/*.schema.json`.

### 1. Canonical URI vs hosted URI

- Canonical schema identifier (`$id`): `https://ae-framework/schema/<file>`
- Hosted retrieval URL (GitHub Pages): `https://itdojp.github.io/ae-framework/schema/<file>`

Use `https://ae-framework/schema/<file>` as the canonical identifier for new or migrated schemas.  
Use `https://itdojp.github.io/ae-framework/schema/<file>` as the hosted access endpoint when a directly dereferenceable URL is required.

### 2. Current implementation snapshot (as-is)

Most schemas already use `https://ae-framework/schema/<file>`.  
The following schemas currently keep GitHub Pages-based `$id` for compatibility:

- `schema/codex-task-request.schema.json`
- `schema/codex-task-response.schema.json`
- `schema/quality-report.schema.json`
- `schema/verify-profile-summary.schema.json`

### 3. Anti-pattern (forbidden)

Do not use repository URLs directly in `$id` or `$ref`:

- `https://github.com/itdojp/ae-framework/.../schema/<file>`
- `https://raw.githubusercontent.com/itdojp/ae-framework/.../schema/<file>`

These URLs are branch/path-coupled and are not stable schema identifiers.

### 4. Why this policy

- Keep schema identity independent from hosting location.
- Preserve backward compatibility for already consumed legacy schema IDs.
- Prevent accidental dependence on mutable GitHub repository paths.

### 5. Operational rules

- Keep `<file>` in URI exactly equal to the schema filename under `schema/`.
- If changing `$id` of an already published schema, treat it as compatibility-impacting and follow `docs/project/RELEASE.md`.
- Every `schema/*.schema.json` file must define `$id`.

### 6. Review checklist

- `$id` follows canonical/legacy exception rules above.
- No `github.com` or `raw.githubusercontent.com` URL appears in `$id`/`$ref`.
- Compatibility impact is assessed when `$id` changes.
- Related docs and fixtures are updated.

### 7. CI checkpoints

- `schema/**` changes trigger `.github/workflows/spec-validation.yml`.
- Schema/artifact validation is executed in:
  - `.github/workflows/validate-artifacts-ajv.yml`
  - `.github/workflows/verify-lite.yml`
  - `.github/workflows/minimal-pipeline.yml`
- Documentation consistency is checked by `pnpm docs:lint`.

### 8. Payload versioning (`schemaVersion` / `contractId`)

- `schemaVersion` is a payload compatibility marker; `$id` and `$schema` are schema-identifier metadata. Treat them separately.
- Allowed forms in current implementation:
  - semver (`1.0.0`) for schema families that already use semantic versioning.
  - contract-style (`<contract>/v1`) as a fixed `const` value for contract families managed by major line.
- `contractId` is a stable contract family identifier (example: `pr-state.v1`, `execution-plan.v1`) and should be fixed by schema `const` when present.
- New machine-readable artifacts should include at least one explicit compatibility key (`schemaVersion` or `contractId`); include both when the producer has long-lived consumers.
- Mixed version expression inside one contract family is forbidden. Choose one migration target and keep dual-read compatibility during transition.

### 9. Dual-write / dual-validate migration rules

- When introducing breaking changes, do not overwrite the existing schema/artifact contract in place.
- Use migration phases:
  1. **Dual-write**: producer emits old and new payloads side by side.
  2. **Dual-validate**: CI validates both payloads against their corresponding schemas.
  3. **Cutover**: switch default consumer to new payload.
  4. **Retire**: remove old payload after deprecation window and evidence review.
- During dual period, define:
  - canonical payload (`new` or `old`)
  - start/end condition (issue-based)
  - rollback rule and flag strategy
  - required fixture/test updates

### 10. Breaking-change checklist (schema contracts)

- Breaking examples:
  - removing/renaming required fields
  - changing field type or narrowing enum/pattern in incompatible ways
  - changing semantic meaning without compatibility adapter
  - changing `$id`, `schemaVersion`, or `contractId` compatibility boundary
- Required in the same PR:
  - new schema file / new fixture updates
  - dual-read or migration adapter updates
  - CI validation update (`scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs` as needed)
  - release note entry and migration note (`docs/project/RELEASE.md`)
  - contract catalog update (`docs/reference/CONTRACT-CATALOG.md`)

---

## 日本語

本ドキュメントは、`schema/*.schema.json` における JSON Schema 識別子 URI の運用方針を定義します。

### 1. canonical URI と hosted URI の役割

- canonical なスキーマ識別子（`$id`）: `https://ae-framework/schema/<file>`
- 配布・参照用 hosted URL（GitHub Pages）: `https://itdojp.github.io/ae-framework/schema/<file>`

新規追加または移行対象のスキーマは、`$id` に `https://ae-framework/schema/<file>` を使用します。  
`https://itdojp.github.io/ae-framework/schema/<file>` は、直接取得可能な公開 URL が必要な場面で利用します。

### 2. 現状実装スナップショット（as-is）

大半のスキーマは `https://ae-framework/schema/<file>` を採用しています。  
以下は互換性維持のため、現時点で GitHub Pages ベースの `$id` を保持します。

- `schema/codex-task-request.schema.json`
- `schema/codex-task-response.schema.json`
- `schema/quality-report.schema.json`
- `schema/verify-profile-summary.schema.json`

### 3. Anti-pattern（禁止）

`$id` / `$ref` に GitHub リポジトリ URL を直接使わないこと。

- `https://github.com/itdojp/ae-framework/.../schema/<file>`
- `https://raw.githubusercontent.com/itdojp/ae-framework/.../schema/<file>`

これらはブランチやパスに依存し、安定識別子として不適切です。

### 4. この方針の変更理由

- スキーマ識別子と配布基盤を分離し、運用変更に強くするため。
- 既存利用者が参照する legacy `$id` 互換性を維持するため。
- GitHub URL への暗黙依存を排除し、識別子の安定性を担保するため。

### 5. 運用ルール

- URI の `<file>` は `schema/` 配下の実ファイル名と一致させる。
- 公開済みスキーマの `$id` 変更は互換性影響ありとして扱い、`docs/project/RELEASE.md` の手順に従う。
- `schema/*.schema.json` は `$id` 定義を必須とする。

### 6. レビュー観点

- `$id` が canonical/例外ルールに準拠しているか。
- `$id` / `$ref` に `github.com` / `raw.githubusercontent.com` が混入していないか。
- `$id` 変更時に互換性評価が実施されているか。
- 関連ドキュメント・fixtures の更新が揃っているか。

### 7. CI観点

- `schema/**` の変更は `.github/workflows/spec-validation.yml` のトリガー対象。
- スキーマ/成果物検証は次で実行される。
  - `.github/workflows/validate-artifacts-ajv.yml`
  - `.github/workflows/verify-lite.yml`
  - `.github/workflows/minimal-pipeline.yml`
- ドキュメント整合は `pnpm docs:lint` で確認する。

### 8. ペイロード版管理（`schemaVersion` / `contractId`）

- `schemaVersion` はペイロード互換性の識別子、`$id` / `$schema` はスキーマ識別子です。役割を分離して扱います。
- 現行実装で許容される形式:
  - semver（`1.0.0`）: 既存で semantic versioning を採用している契約系列
  - 契約識別子型（`<contract>/v1`）: major 系列を `const` で固定する契約系列
- `contractId` は契約系列の安定識別子（例: `pr-state.v1`, `execution-plan.v1`）であり、存在する場合は schema 側で `const` 固定します。
- 新規の機械可読成果物は、互換境界キー（`schemaVersion` または `contractId`）を最低1つ持つこと。長期消費される成果物は両方を持つことを推奨します。
- 同一契約系列内で版表現を混在させないこと。移行時は dual-read 互換期間を明示します。

### 9. dual-write / dual-validate 運用ルール

- 互換性破壊を伴う変更では、既存契約を上書き変更しません。
- 移行は次の段階で実施します。
  1. **dual-write**: producer が旧/新ペイロードを並行出力
  2. **dual-validate**: CI で旧/新の両方を対応 schema で検証
  3. **cutover**: consumer の既定読取を新契約へ切替
  4. **retire**: 互換期間終了後に旧契約を廃止
- dual 期間では以下を必ず定義します。
  - canonical payload（旧/新どちらを正とするか）
  - 開始/終了条件（追跡Issue）
  - ロールバック手順と feature flag 戦略
  - 必須 fixture / test 更新

### 10. 互換性破壊チェックリスト（schema契約）

- 破壊的変更の例:
  - required フィールドの削除/改名
  - 型変更、enum/pattern の非互換な狭小化
  - 互換アダプタなしの意味変更
  - `$id` / `schemaVersion` / `contractId` の互換境界変更
- 同一PRで必須とする更新:
  - 新版 schema と fixture の追加更新
  - dual-read または移行アダプタの更新
  - CI検証更新（必要に応じて `scripts/ci/validate-json.mjs`, `scripts/ci/validate-artifacts-ajv.mjs`）
  - リリースノートと移行注記（`docs/project/RELEASE.md`）
  - 契約カタログ更新（`docs/reference/CONTRACT-CATALOG.md`）
