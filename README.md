# Minimal-Human, Spec-First Starter

> 人手最小＆仕様準拠最大。Intent→Formal→Tests→Code→Verify→Operate の6フェーズ。

## Quick Start (WSL + Podman)

```bash
# 1) 依存セットアップ（WSL Ubuntu）
./scripts/dev/setup_wsl.sh

# 2) 開発環境起動（API + Postgres + OTel Collector）
./scripts/dev/dev_up.sh

# 3) 仕様→テスト→実行
make spec:lint test:all

# 4) ローカルCI一括
./scripts/ci/run_all_local.sh
```

### 主要コマンド（Makefile）

- `make spec:lint` — Gherkin/OpenAPI/SLOのLint & 曖昧語検査
- `make formal:check` — TLA+ (Apalache) モデル検査
- `make test:acceptance` — BDD→E2E(API) 実行
- `make test:property` — PBT
- `make test:mbt` — モデルベーステスト
- `make test:contract` — Pact
- `make test:mutation` — Mutation (Stryker)
- `make test:api-fuzz` — Schemathesis (OpenAPI fuzz)
- `make policy:test` — OPA/Rego テスト
- `make sbom` — Syft/CycloneDX で SBOM 生成
- `make verify:trace` — 仕様↔テスト↔実装の対応表

### 置き換えやすさ

- 言語/ランタイム: `src/` を他言語に差し替え可（Rust/Deno等）
- DB: `compose.yaml` の `postgres` を別エンジンに変更可
- 本番: Terraform/Ansible/Helm/Kustomize いずれにも拡張可