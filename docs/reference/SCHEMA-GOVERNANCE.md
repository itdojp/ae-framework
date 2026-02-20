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
