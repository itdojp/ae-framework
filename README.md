# ae-framework: AI-Agent Enabled Framework

> 人手最小＆仕様準拠最大。TDD強制機能付きIntent→Formal→Tests→Code→Verify→Operate の6フェーズ。

## 🚀 AI-Powered Development Features

### 🤖 Test Generation Agent (NEW!)
自動的に包括的なテストを生成する AI エージェント：

- **要件からテスト生成**: 自然言語の要件から完全なテストスイートを作成
- **コードからテスト逆生成**: 既存コードを分析してテストを生成（リバースTDD）
- **Property-Based Testing**: 数学的性質からプロパティテストを自動設計
- **BDD シナリオ生成**: ユーザーストーリーから Gherkin シナリオを作成
- **セキュリティテスト**: OWASP ガイドラインに基づくセキュリティテスト生成
- **パフォーマンステスト**: SLA 要件からパフォーマンステストスイートを設計

```bash
# MCP サーバーとして起動
npm run mcp:test-gen

# 使用例
{
  "tool": "generate_tests_from_requirements",
  "args": {
    "feature": "User Authentication",
    "requirements": ["Users can login", "Password must be hashed"]
  }
}
```

### 🛡️ TDD Enforcement Features
TDD（Test-Driven Development）原則の遵守を自動的に強制：

### 🛡️ TDD Guards
- **TDD Guard**: コードファイルに対応するテストファイルの存在を強制
- **Test Execution Guard**: コミット前の全テスト通過を確認
- **RED-GREEN Cycle Guard**: RED→GREEN→REFACTORサイクルの遵守をチェック
- **Coverage Guard**: 最低カバレッジ（80%）の維持を監視

### 📋 Phase Validation
各フェーズで必要な成果物とバリデーションを自動チェック：
- **Phase 3 (Tests)**: テストが最初に失敗することを確認（RED phase）
- **Phase 4 (Code)**: 実装後にテストが通ることを確認（GREEN phase）
- **Phase 5 (Verify)**: 全テストスイート実行とカバレッジ確認

### 🔧 CLI Tools
```bash
# 現在フェーズの要件をチェック
ae-framework check --phase 3-tests

# TDDガードを実行
ae-framework guard

# 次のフェーズに進む準備ができているか確認
ae-framework next

# TDDサイクル全体を検証
ae-framework tdd
```

### 🏗️ Setup TDD Enforcement

```bash
# 1) Install ae-framework CLI
npm install -g ae-framework

# 2) Setup Git hooks for TDD enforcement
npm run setup-hooks

# 3) Initialize ae-framework configuration
# Creates ae-framework.yml with TDD settings
ae-framework init
```

## Quick Start (WSL + Podman)

```bash
# 1) 依存セットアップ（WSL Ubuntu）
./scripts/dev/setup_wsl.sh

# 2) TDD enforcement setup
npm run setup-hooks

# 3) 開発環境起動（API + Postgres + OTel Collector）
./scripts/dev/dev_up.sh

# 4) TDD準拠開発
ae-framework check    # 現在のフェーズを確認
make spec:lint test:all

# 5) ローカルCI一括
./scripts/ci/run_all_local.sh
```

### 📝 TDD Development Workflow

```bash
# Phase 1: Intent (Requirements)
ae-framework check --phase 1-intent

# Phase 2: Formal Specifications  
ae-framework check --phase 2-formal

# Phase 3: Test-First (RED)
ae-framework check --phase 3-tests
npm test  # Should FAIL initially

# Phase 4: Implementation (GREEN)
ae-framework check --phase 4-code  
npm test  # Should PASS after implementation

# Phase 5: Verification
ae-framework check --phase 5-verify
npm run coverage  # Should be >= 80%

# Phase 6: Operations
ae-framework check --phase 6-operate
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