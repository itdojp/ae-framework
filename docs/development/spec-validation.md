---
docRole: ssot
lastVerified: '2026-03-11'
owner: development-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# AE-Spec Validation System

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

The AE-Framework includes a comprehensive specification validation system that ensures quality and consistency of AE-Spec files throughout the development lifecycle.

## Overview

The validation system consists of:

- **GitHub Actions Workflow**: Automated validation on PR and push
- **Local Validation Scripts**: Developer tools for pre-commit validation  
- **Quality Gates**: Configurable thresholds for errors, warnings, and info messages
- **Pre-commit Hooks**: Automatic validation before commits

## Components

### 1. GitHub Actions Workflow

**File**: `.github/workflows/spec-validation.yml`

Automatically runs on:
- Push to `main` branch (when spec files change)
- Pull requests to `main` branch (when spec files change)
- Changes to spec-compiler package

**Features**:
- ✅ Validates all AE-Spec files in `spec/` directory
- ✅ Configurable quality thresholds (errors/warnings)
- ✅ PR comments with validation results
- ✅ Artifact upload for validation results
- ✅ Quality gates check

### 2. Validation Configuration

**File**: `.ae/spec-validation.config.json`

Defines validation rules and thresholds:

```json
{
  "quality_gates": {
    "max_errors": 0,
    "max_warnings": 10,
    "fail_on_missing_sections": true
  },
  "validation_rules": {
    "structure": { "STRUCT_001": "error", ... },
    "business_logic": { "BIZ_001": "warn", ... },
    "consistency": { "CONS_001": "error", ... },
    "completeness": { "COMP_001": "warn", ... }
  }
}
```

### 3. Local Validation Script

**File**: `scripts/validate-specs.sh`

**Usage**:
```bash
# Validate all specs
pnpm run validate:specs

# Validate specific file
pnpm run validate:spec spec/my-spec.md

# Direct script usage
./scripts/validate-specs.sh
./scripts/validate-specs.sh -f spec/my-spec.md
./scripts/validate-specs.sh --help
```

**Features**:
- Colored output for better readability
- Summary reporting (total/passed/failed)
- Individual file results
- Configuration file support
- Verbose and quiet modes

### 4. Pre-commit Hook

**File**: `scripts/hooks/pre-commit-spec-validation`

**Setup**:
```bash
pnpm run hooks:setup-spec-validation
```

**Features**:
- Only validates modified `.md` files in `spec/` directory
- Blocks commits if validation fails
- Shows detailed error messages
- Can be bypassed with `--no-verify` (not recommended)

## Validation Rules

### Structure Rules (STRUCT)

| Rule ID | Severity | Description |
|---------|----------|-------------|
| STRUCT_001 | error | Specification must have a name in metadata |
| STRUCT_002 | warn | At least one domain entity should be defined |
| STRUCT_003 | info | API endpoints should be documented |

### Business Logic Rules (BIZ)

| Rule ID | Severity | Description |
|---------|----------|-------------|
| BIZ_001 | warn | Entities should have associated business rules |

### Consistency Rules (CONS)

| Rule ID | Severity | Description |
|---------|----------|-------------|
| CONS_001 | error | Entity relationships must reference existing entities |

### Completeness Rules (COMP)

| Rule ID | Severity | Description |
|---------|----------|-------------|
| COMP_001 | warn | Entities should have at least one required field |

## Quality Thresholds

Default quality gates:
- **Errors**: 0 (any error fails validation)
- **Warnings**: 10 (more than 10 warnings fails validation)
- **Info**: unlimited

## Lenient Mode (Development)

To accelerate early iteration, a lenient validation profile is available:

- Env flag: `AE_SPEC_RELAXED=1` downgrades strict schema errors to warnings.
- Root CLI: `ae-framework spec validate --relaxed` enables lenient mode.
- Package CLI: `ae-spec validate --relaxed` also supported.
- Increase warning tolerance for local runs with `--max-warnings 999` or via `.ae/spec-validation.config.json`.

Configurable limits (via environment variables):
- `AE_SPEC_DESC_MIN` / `AE_SPEC_DESC_MAX`: common description length (default 10/500)
- `AE_SPEC_FIELD_DESC_MAX` / `AE_SPEC_DOMAIN_DESC_MAX` / `AE_SPEC_INVARIANT_DESC_MAX`
- `AE_SPEC_GLOSSARY_DESC_MAX`
- API-related: `AE_SPEC_API_SUMMARY_MAX`, `AE_SPEC_API_PARAM_DESC_MAX`, `AE_SPEC_API_ERROR_DESC_MAX`
- Constraint length: `AE_SPEC_CONSTRAINT_MAX`

CLI overrides:
- Root CLI: `ae-framework spec validate --relaxed --desc-max 2000`
- Package CLI: `ae-spec compile --relaxed --desc-max 2000`

Lenient normalizations:
- Field type hints like `enum: a|b` are coerced to `string` in lenient mode.
- Invariant ID auto-fallback: non-UUID IDs are replaced with generated UUIDv4 in lenient mode.

Note: CI should continue using the strict profile by default.

## Usage Scenarios

### 1. Developer Workflow

```bash
# 1. Create/modify specification
vim spec/my-new-feature.md

# 2. Validate locally
pnpm run validate:spec spec/my-new-feature.md

# 3. Fix any issues and re-validate
pnpm run validate:spec spec/my-new-feature.md

# 4. Commit (pre-commit hook validates automatically)
git add spec/my-new-feature.md
git commit -m "feat: add new feature specification"
```

### 2. CI/CD Integration

The GitHub Actions workflow automatically:
1. Detects changed spec files
2. Builds spec-compiler
3. Validates all modified specifications
4. Comments on PR with results
5. Uploads validation artifacts
6. Fails build if quality gates not met

### 3. Team Standards Enforcement

- **Quality gates** ensure minimum standards
- **Pre-commit hooks** catch issues early
- **PR validation** prevents bad specs from merging
- **Configurable rules** allow team customization

## Troubleshooting

### Common Issues

1. **"spec-compiler not found"**
   ```bash
   cd packages/spec-compiler
   pnpm run build
   ```

2. **"Validation failed: Entity has no business rules"**
   - Add invariants section referencing the entity
   - Example: `User email must be unique`

3. **"Entity references undefined entity"**
   - Ensure all relationship targets exist
   - Check entity name spelling

4. **"No required fields defined"**
   - Mark important fields as `required`
   - Example: `**id** (UUID, required)`

### Debug Mode

For detailed validation output:
```bash
./scripts/validate-specs.sh -v
```

### Configuration Validation

Test your configuration:
```bash
cd packages/spec-compiler
node dist/cli.js validate -i ../../.ae/spec-validation.config.json
```

## Integration with Development Tools

### VS Code

Add to `.vscode/tasks.json`:
```json
{
  "label": "Validate Current Spec",
  "type": "shell",
  "command": "./scripts/validate-specs.sh",
  "args": ["-f", "${file}"],
  "group": "test",
  "presentation": {
    "echo": true,
    "reveal": "always"
  }
}
```

### Git Aliases

Add to `.gitconfig`:
```ini
[alias]
  validate-specs = !pnpm run validate:specs
  validate-spec = "!f() { pnpm run validate:spec \"$1\"; }; f"
```

## Best Practices

1. **Run validation locally** before pushing
2. **Fix errors immediately** - don't let them accumulate
3. **Review validation output** in PR comments
4. **Update configuration** as team standards evolve
5. **Use descriptive commit messages** when fixing validation issues
6. **Keep specifications up-to-date** with implementation

## Monitoring and Metrics

The validation system tracks:
- Success/failure rates per specification
- Common validation issues
- Time to fix validation problems
- Quality trend over time

Results are stored in `artifacts/validation-results/` directory and uploaded as CI artifacts for analysis.

---

## Japanese

**AE-Spec 検証システム**

AE-Framework には、開発ライフサイクル全体を通してAE-Specファイルの品質と一貫性を保証する包括的な仕様検証システムが含まれています。

## 概要

検証システムは以下で構成されています：

- **GitHub Actions ワークフロー**: PR およびプッシュ時の自動検証
- **ローカル検証スクリプト**: 開発者向けのコミット前検証ツール
- **品質ゲート**: エラー、警告、情報メッセージの設定可能な閾値
- **プリコミットフック**: コミット前の自動検証

## コンポーネント

### 1. GitHub Actions ワークフロー

**ファイル**: `.github/workflows/spec-validation.yml`

以下の場合に自動実行：
- `main` ブランチへのプッシュ（仕様ファイルに変更がある場合）
- `main` ブランチへのプルリクエスト（仕様ファイルに変更がある場合）
- spec-compiler パッケージの変更

**機能**:
- ✅ `spec/` ディレクトリ内のすべてのAE-Specファイルを検証
- ✅ 設定可能な品質閾値（エラー/警告）
- ✅ 検証結果のPRコメント
- ✅ 検証結果のアーティファクトアップロード
- ✅ 品質ゲートチェック

### 2. ローカル検証スクリプト

**ファイル**: `scripts/validate-specs.sh`

```bash
# すべての仕様を検証
./scripts/validate-specs.sh

# 特定ファイルを検証
./scripts/validate-specs.sh -f spec/user-management.md

# エラー時に詳細表示
./scripts/validate-specs.sh --verbose

# JSON形式で結果出力
./scripts/validate-specs.sh --format json
```

### 3. 品質ゲート設定

品質閾値は`.ae/spec-validation.config.json`で設定：

```json
{
  "thresholds": {
    "errors": 0,           // エラー許容数（0推奨）
    "warnings": 5,         // 警告許容数
    "info": 10            // 情報メッセージ許容数
  },
  "failOnThresholdExceeded": true,
  "outputFormat": "both"   // "console", "json", "both"
}
```

## 使用方法

### 開発ワークフロー

```bash
# 1. 仕様ファイルを編集
vim spec/user-management.md

# 2. ローカル検証実行
./scripts/validate-specs.sh -f spec/user-management.md

# 3. 問題を修正
# （検証エラーに基づいて仕様を修正）

# 4. 再検証
./scripts/validate-specs.sh -f spec/user-management.md

# 5. コミット（プリコミットフックが自動実行）
git add spec/user-management.md
git commit -m "feat: ユーザー管理仕様を更新"
```

### CI/CD統合

```yaml
# GitHub Actionsワークフロー例
name: AE-Spec検証
on:
  push:
    branches: [main]
    paths: ['spec/**/*.md', 'packages/spec-compiler/**']
  pull_request:
    branches: [main]
    paths: ['spec/**/*.md']

jobs:
  validate-specs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: AE-Spec検証実行
        run: |
          chmod +x scripts/validate-specs.sh
          ./scripts/validate-specs.sh
      
      - name: 検証結果をアップロード
        uses: actions/upload-artifact@v4
        if: always()
        with:
          name: spec-validation-results
          path: artifacts/validation-results/
```

## スクリプト

```json
{
  "scripts": {
    "validate:specs": "./scripts/validate-specs.sh",
    "validate:spec": "./scripts/validate-specs.sh -f",
    "validate:specs:json": "./scripts/validate-specs.sh --format json",
    "validate:specs:verbose": "./scripts/validate-specs.sh --verbose"
  }
}
```

## プリコミットフック

**ファイル**: `.husky/pre-commit`

```bash
#!/usr/bin/env sh
. "$(dirname -- "$0")/_/husky.sh"

# AE-Spec検証を実行
echo "🔍 AE-Spec検証を実行中..."
./scripts/validate-specs.sh

if [ $? -ne 0 ]; then
  echo "❌ AE-Spec検証に失敗しました。修正してから再度コミットしてください。"
  exit 1
fi

echo "✅ AE-Spec検証が完了しました。"
```

## 設定例

### 基本設定

```json
{
  "validation": {
    "enabled": true,
    "rules": {
      "syntax": "strict",
      "completeness": "warn",
      "consistency": "error"
    }
  },
  "thresholds": {
    "errors": 0,
    "warnings": 3,
    "info": 5
  },
  "exclude": [
    "spec/draft/**",
    "spec/archive/**"
  ]
}
```

### 高度な設定

```json
{
  "validation": {
    "customRules": [
      {
        "name": "requirement-coverage",
        "severity": "warning",
        "pattern": "^## Requirements$",
        "message": "要件セクションが見つかりません"
      }
    ],
    "plugins": [
      "@ae-framework/spec-lint-japanese"
    ]
  },
  "reporting": {
    "format": ["console", "json", "junit"],
    "outputDir": "./artifacts/validation-results"
  }
}
```

## 開発ツール統合

### VS Code

`.vscode/tasks.json` に追加：

```json
{
  "label": "現在の仕様を検証",
  "type": "shell",
  "command": "./scripts/validate-specs.sh",
  "args": ["-f", "${file}"],
  "group": "test",
  "presentation": {
    "echo": true,
    "reveal": "always"
  }
}
```

### Git エイリアス

`.gitconfig` に追加：

```ini
[alias]
  validate-specs = !pnpm run validate:specs
  validate-spec = "!f() { pnpm run validate:spec \"$1\"; }; f"
```

## ベストプラクティス

1. **ローカルで検証実行** - プッシュ前に実行
2. **エラーの即座修正** - 蓄積させない
3. **PRコメントの検証結果レビュー** - 品質確認
4. **設定の更新** - チーム標準の進化に合わせて
5. **わかりやすいコミットメッセージ** - 検証問題修正時
6. **仕様の最新化** - 実装との同期維持

## 監視と指標

検証システムが追跡する項目：
- 仕様ごとの成功/失敗率
- 一般的な検証問題
- 検証問題の修正時間
- 時系列での品質トレンド

結果は `artifacts/validation-results/` ディレクトリに保存され、分析用にCIアーティファクトとしてアップロードされます。
