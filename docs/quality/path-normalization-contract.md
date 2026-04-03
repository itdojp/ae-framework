---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-04-04'
---
# Path Normalization Contract（Artifacts/Reports）

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
When artifact or report JSON includes environment-specific absolute paths or inconsistent separators, pull request diffs become noisy and outputs stop being portable across local and CI environments.

This contract standardizes how path-like fields are written inside generated JSON artifacts and reports.

### 2. Normalization rules
1. If the input is already relative, keep it relative but normalize separators to `/`
2. If the input is absolute and inside the repository, convert it to a repo-relative path
3. If the input is absolute and outside the repository, keep it absolute so the external dependency remains explicit
4. Always normalize path separators to POSIX-style `/`

Notes:
- Do not rewrite external absolute paths to `../..` style relative paths
- Windows-originated paths such as `C:\\...` or `\\\\server\\share\\...` should remain external absolute paths on POSIX hosts, but their displayed separators should still be normalized to `C:/...` or `//server/share/...`

### 3. Example target fields
- `artifacts[].path` in report envelope style outputs
- `*.file`, `detailsFile`, `logPath`, `summaryPath` in formal or conformance summary JSON
- `sources.*` in aggregate JSON such as progress summaries

### 4. Implementation reference
The repository treats the following as the standard implementations:
- Node scripts: `scripts/ci/lib/path-normalization.mjs` -> `normalizeArtifactPath()`
- TypeScript: `src/utils/path-normalization.ts` -> `normalizeArtifactPath()`

Call sites should normally pass `repoRoot: process.cwd()`, which is expected to be the repository root at execution time.

### 5. Examples
- Input: `/home/runner/work/repo/repo/artifacts/report-envelope.json` -> Output: `artifacts/report-envelope.json`
- Input: `/tmp/tool.log` -> Output: `/tmp/tool.log`
- Input: `reports\\lint\\verify-lite-lint-summary.json` -> Output: `reports/lint/verify-lite-lint-summary.json`
- Input: `\\\\server\\share\\artifact.json` -> Output: `//server/share/artifact.json`

---

## 日本語

### 1. 目的
成果物（artifacts/reports）JSON に環境依存の絶対パスや区切り文字の揺れが混入すると、PR差分ノイズや可搬性低下が発生します。本契約は、**生成物JSONに含めるパス表現**を標準化します。

### 2. 正規化ルール（契約）
1. 入力が相対パスなら相対のまま保持（ただし区切りを`/`へ正規化）
2. 入力が絶対パスで repo 配下なら **リポジトリ相対パス** に変換
3. repo 外の絶対パスは絶対のまま保持（外部依存として明示）
4. 区切り文字は常に`/`（POSIX形式）へ正規化

補足:
- repo 外パスを `../..` のような相対表現に落とさない（差分安定性と可読性のため）
- Windows 由来の `C:\\...` / `\\\\server\\share\\...` は、POSIXホスト上では外部絶対として扱い、`C:/...` / `//server/share/...` のように表記のみ正規化します

### 3. 適用対象フィールド（例）
- `artifacts[].path`（report envelope 等）
- `*.file` / `detailsFile` / `logPath` / `summaryPath`（formal/conformance 系の要約JSON）
- `sources.*`（progress summary 等の集約JSON）

### 4. 実装（参照）
本リポジトリでは、次の関数を標準実装として扱います。
- Node scripts: `scripts/ci/lib/path-normalization.mjs` の `normalizeArtifactPath()`
- TypeScript: `src/utils/path-normalization.ts` の `normalizeArtifactPath()`

呼び出し側は、原則 `repoRoot: process.cwd()`（= 実行時のリポジトリルート）を指定します。

### 5. 例
- 入力: `/home/runner/work/repo/repo/artifacts/report-envelope.json`（repo配下絶対） → 出力: `artifacts/report-envelope.json`
- 入力: `/tmp/tool.log`（repo外絶対） → 出力: `/tmp/tool.log`
- 入力: `reports\\lint\\verify-lite-lint-summary.json`（Windows区切り） → 出力: `reports/lint/verify-lite-lint-summary.json`
- 入力: `\\\\server\\share\\artifact.json`（UNC） → 出力: `//server/share/artifact.json`
