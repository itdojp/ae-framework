---
docRole: ssot
lastVerified: '2026-03-23'
owner: development-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Centralized Quality Gates System

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Comprehensive centralized quality gates system ensuring consistent quality standards across all development phases and environments**

The AE-Framework implements a comprehensive centralized quality gates system that ensures consistent quality standards across all development phases and environments.

## Overview

The centralized quality gates system provides:

- **Single Source of Truth**: All quality thresholds defined in one JSON configuration file
- **Environment-Specific Overrides**: Different standards for development, CI, and production
- **Phase-Aware Enforcement**: Quality gates activate based on development phase progression
- **Automated CI/CD Integration**: GitHub Actions workflows enforce quality standards
- **Flexible Configuration**: Easy to modify thresholds and add new quality gates

### Current Repository Baseline

In the current repository, day-to-day pull requests are primarily gated by:

- `verify-lite`
- `policy-gate`
- `gate`

This document still matters because it describes the centralized quality-threshold subsystem that feeds local quality runs, compatibility aliases such as `quality:gates`, and conditional or specialized workflows. It should not be read as saying that `quality-gates-centralized.yml` is the only required PR baseline.

## Architecture

### Core Components

```
policy/
├── quality.json              # Centralized policy configuration
src/utils/
├── quality-policy-loader.ts  # TypeScript utility for loading policy
scripts/
├── run-quality-gates.cjs     # Compatibility entrypoint
├── quality/run.mjs           # Maintained quality runner
├── check-a11y-threshold.cjs  # Accessibility checker (updated)
├── check-coverage-threshold.cjs # Coverage checker (new)
.github/workflows/
├── quality-gates-centralized.yml # Centralized quality workflow support
└── phase6-validation.yml     # Updated to use centralized policy
```

### Policy Configuration Structure

The centralized policy (`policy/quality.json`) defines:

1. **Quality Gates**: Each gate has thresholds, enforcement level, applicable phases, and tools
2. **Environment Overrides**: Specific adjustments for dev/CI/production environments  
3. **Reporting Configuration**: Output formats, retention, and notification settings
4. **Tool Integration**: Configuration for external tools like Lighthouse CI

## Configuration

### Quality Gates Definition

Each quality gate is defined with:

```text
{
  "gateName": {
    "description": "Human-readable description",
    "enforcement": "strict|warn|off",
    "thresholds": {
      "metricName": value
    },
    "tools": ["tool1", "tool2"],
    "phases": ["phase-3", "phase-6"],
    "enabledFromPhase": "phase-3",
    "excludePatterns": ["**/*.d.ts"]
  }
}
```

### Supported Quality Gates

| Gate | Description | Key Metrics | Phases |
|------|-------------|-------------|---------|
| **accessibility** | A11y compliance | critical≤0, warnings≤5 | phase-6 |
| **coverage** | Code coverage | lines≥80%, functions≥80% | phase-3+ |
| **lighthouse** | Performance & quality | performance≥90, a11y≥95 | phase-6 |
| **linting** | Code quality & style | errors≤0, warnings≤10 | all |
| **security** | Vulnerability scan | critical≤0, high≤0 | phase-4+ |
| **tdd** | Test-driven development | ratio≥1.2, compliance≥100% | phase-3+ |
| **visual** | Visual regression | pixelDiff≤0.02 | phase-6 |
| **policy** | OPA compliance | violations≤0 | phase-6 |
| **mutation** | Mutation testing | score≥70% | phase-4+ |

### Environment Overrides

#### Development Environment
- Relaxed thresholds for faster iteration
- Warnings instead of strict enforcement
- Some gates disabled (lighthouse, visual)

#### CI Environment  
- Standard enforcement levels
- All applicable gates enabled
- Balanced between quality and build speed

#### Production Environment
- Strictest thresholds
- Zero tolerance for critical issues
- Enhanced security and performance requirements

## Usage

### Command Line Interface

#### Basic Usage
```bash
# Run all applicable quality gates for current phase
pnpm run quality:gates

# Run with specific environment
pnpm run quality:gates:dev
pnpm run quality:gates:prod

# Run specific gates only
pnpm run quality:run:accessibility
pnpm run quality:run:coverage

# Run comprehensive quality check
pnpm run quality:run:all
```

#### Advanced Usage
```bash
# Custom environment and phase
node scripts/run-quality-gates.cjs --env=production --phase=phase-6

# Specific gate combination
node scripts/run-quality-gates.cjs --gates=accessibility,coverage,lighthouse

# Help and options
node scripts/run-quality-gates.cjs --help
```

### TypeScript Integration

```text
import { 
  loadQualityPolicy, 
  getQualityGate, 
  shouldEnforceGate,
  validateQualityResults 
} from '../src/utils/quality-policy-loader.js';

// Load policy with environment overrides
const policy = loadQualityPolicy('ci');

// Get specific gate configuration  
const accessibilityGate = getQualityGate('accessibility', 'ci');

// Check if gate should be enforced
const shouldCheck = shouldEnforceGate('accessibility', 'phase-6', 'ci');

// Validate results against thresholds
const validation = validateQualityResults('accessibility', {
  critical: 0,
  serious: 1,
  moderate: 2
}, 'ci');
```

### GitHub Actions Integration

The system automatically integrates with GitHub Actions:

```yaml
# Use the centralized quality gates workflow
name: Quality Check
on: [push, pull_request]

jobs:
  quality:
    uses: ./.github/workflows/quality-gates-centralized.yml
    with:
      environment: 'ci'
      phase: 'auto-detect'
      gates: 'all'
```

Current operations also run this subsystem alongside the repository baseline checks (`verify-lite`, `policy-gate`, `gate`) rather than instead of them.

## Implementation Details

### Policy Loading and Overrides

The policy loader applies environment-specific overrides using a dot-notation path system:

```text
{
  "environments": {
    "development": {
      "overrides": {
        "accessibility.thresholds.total_warnings": 10,
        "coverage.enforcement": "warn"
      }
    }
  }
}
```

### Phase-Aware Enforcement

Quality gates can be configured to:
1. Apply to specific phases: `"phases": ["phase-6"]`
2. Enable from a certain phase onward: `"enabledFromPhase": "phase-3"`
3. Always apply if no phase restrictions are defined

### Tool Integration

#### Lighthouse CI
- Dynamic configuration based on policy thresholds  
- Environment-aware assertion levels
- Automatic score conversion (90 → 0.9)

#### Coverage Tools
- Support for both nyc and vitest coverage
- Configurable exclude patterns
- Multiple metric types (lines, functions, branches, statements)

#### Accessibility Testing
- Integration with jest-axe and axe-core
- Multi-level violation tracking
- Detailed failure reporting

### Error Handling and Fallbacks

The system includes robust error handling:

1. **Policy Loading Failures**: Falls back to CLI arguments or defaults
2. **Tool Unavailability**: Skips gates for missing tools with warnings
3. **Report Generation**: Creates empty reports for development environments
4. **Environment Detection**: Auto-detects environment from NODE_ENV

## Customization

### Adding New Quality Gates

1. **Update Policy Configuration**:
```text
{
  "quality": {
    "myCustomGate": {
      "description": "Custom quality gate",
      "enforcement": "strict",
      "thresholds": {
        "customMetric": 90
      },
      "tools": ["custom-tool"],
      "phases": ["phase-4", "phase-5", "phase-6"]
    }
  }
}
```

2. **Implement Gate Runner**:
```text
// In scripts/run-quality-gates.cjs
case 'myCustomGate':
  command = 'pnpm run <your-custom-check>'; // user-defined example
  break;
```

3. **Add Script**:
```text
{
  "scripts": {
    "quality:custom": "node scripts/run-quality-gates.cjs --gates=myCustomGate"
  }
}
```

### Modifying Thresholds

Simply update the `policy/quality.json` file:

```text
{
  "quality": {
    "coverage": {
      "thresholds": {
        "lines": 85,        // Changed from 80
        "functions": 85     // Changed from 80  
      }
    }
  }
}
```

All tools and workflows will automatically use the new thresholds.

### Environment-Specific Adjustments

Add or modify environment overrides:

```text
{
  "environments": {
    "staging": {
      "description": "Staging environment",
      "overrides": {
        "lighthouse.thresholds.performance": 85,
        "accessibility.enforcement": "warn"
      }
    }
  }
}
```

## Best Practices

### Policy Management
1. **Version Control**: Always version control the policy file
2. **Change Reviews**: Require approval for threshold changes
3. **Documentation**: Document rationale for threshold values
4. **Gradual Changes**: Implement threshold increases gradually

### Development Workflow
1. **Pre-commit**: Run quality gates before committing
2. **Local Testing**: Use development environment for iteration
3. **Phase Awareness**: Understand which gates apply to your current phase
4. **Continuous Monitoring**: Regular quality gate execution

### CI/CD Integration
1. **Matrix Strategy**: Parallel execution for faster feedback
2. **Artifact Collection**: Preserve reports for analysis
3. **Failure Handling**: Appropriate fail-fast vs. continue-on-error
4. **PR Comments**: Automated feedback on pull requests

## Troubleshooting

### Common Issues

#### Policy Loading Failures
```bash
⚠️  Could not load quality policy: ENOENT: no such file or directory
```
**Solution**: Ensure `policy/quality.json` exists and is valid JSON.

#### Phase Detection Problems
```bash
⚠️  Could not detect current phase, using phase-1
```
**Solution**: Create `.ae/phase-state.json` or specify phase explicitly:
```bash
node scripts/run-quality-gates.cjs --phase=phase-6
```

#### Tool Unavailability
```bash
⚠️  Lighthouse CI config not found, skipping
```
**Solution**: Install required tools or configure gate as optional.

### Debug Mode

Enable verbose logging for troubleshooting:

```bash
DEBUG=quality-gates node scripts/run-quality-gates.cjs --env=development
```

### Manual Threshold Validation

Test specific thresholds without running full quality gates:

```bash
# Check accessibility only
node scripts/check-a11y-threshold.cjs --env=development

# Check coverage only  
node scripts/check-coverage-threshold.cjs --env=ci
```

## Migration Guide

### From Hardcoded Thresholds

1. **Identify Current Thresholds**: Review existing scripts and workflows
2. **Update Policy File**: Add current values to `policy/quality.json`
3. **Update Scripts**: Modify to use centralized policy loader
4. **Test Migration**: Verify same behavior with new system
5. **Cleanup**: Remove hardcoded values from scripts

### From Multiple Configuration Files

1. **Consolidate Configurations**: Merge threshold values into single policy
2. **Update Tool Configs**: Modify tools to read from centralized policy
3. **Environment Mapping**: Map existing environment-specific configs
4. **Validation**: Ensure all scenarios still work correctly

## Advanced Features

### Conditional Enforcement

Gates can be conditionally enforced based on:
- File changes (via GitHub Actions path filters)
- Environment variables
- Development phase progression
- Custom business logic

### Reporting Integration

The system supports multiple reporting formats:
- JSON for programmatic consumption
- HTML for human-readable reports  
- JUnit XML for CI/CD integration
- Custom formats via plugins

### Notification System

Configure notifications for:
- Quality gate failures
- Threshold changes requiring approval
- Trend analysis and degradation alerts

This centralized quality gates system provides a robust foundation for maintaining consistent code quality across the entire AE-Framework development lifecycle.

---

## Japanese

**全開発フェーズと環境において一貫した品質基準を保証する包括的な集約品質ゲートシステム**

AE-Frameworkは、全ての開発フェーズと環境において一貫した品質基準を保証する包括的な集約品質ゲートシステムを実装しています。

### 概要

集約品質ゲートシステムは以下を提供します：

- **単一情報源**: 全ての品質閾値を一つのJSON設定ファイルで定義
- **環境固有のオーバーライド**: 開発、CI、本番環境での異なる基準
- **フェーズ認識の強制**: 開発フェーズの進行に基づく品質ゲートの有効化
- **自動CI/CD統合**: GitHub Actionsワークフローによる品質基準の強制
- **柔軟な設定**: 閾値の変更と新しい品質ゲートの追加が容易

### アーキテクチャ

#### コアコンポーネント

```
policy/
├── quality.json              # 集約ポリシー設定
src/utils/
├── quality-policy-loader.ts  # ポリシーロード用TypeScriptユーティリティ
scripts/
├── run-quality-gates.cjs     # 互換エントリポイント
├── quality/run.mjs           # 現行の品質ランナー
├── check-a11y-threshold.cjs  # アクセシビリティチェッカー（更新済み）
├── check-coverage-threshold.cjs # カバレッジチェッカー（新規）
.github/workflows/
├── quality-gates-centralized.yml # 集約品質ワークフロー補助
└── phase6-validation.yml     # 集約ポリシー使用に更新
```

#### ポリシー設定構造

集約ポリシー（`policy/quality.json`）は以下を定義します：

1. **品質ゲート**: 各ゲートは閾値、強制レベル、適用フェーズ、ツールを含む
2. **環境オーバーライド**: dev/CI/本番環境での特定調整
3. **レポート設定**: 出力形式、保持期間、通知設定
4. **ツール統合**: Lighthouse CIなど外部ツールの設定

### 設定

#### 品質ゲート定義

各品質ゲートは以下で定義されます：

```text
{
  "gateName": {
    "description": "人間可読な説明",
    "enforcement": "strict|warn|off",
    "thresholds": {
      "metricName": value
    },
    "tools": ["tool1", "tool2"],
    "phases": ["phase-3", "phase-6"],
    "enabledFromPhase": "phase-3",
    "excludePatterns": ["**/*.d.ts"]
  }
}
```

#### サポートされる品質ゲート

| ゲート | 説明 | 主要メトリクス | フェーズ |
|--------|------|----------------|----------|
| **accessibility** | A11y準拠 | critical≤0, warnings≤5 | phase-6 |
| **coverage** | コードカバレッジ | lines≥80%, functions≥80% | phase-3+ |
| **lighthouse** | パフォーマンス・品質 | performance≥90, a11y≥95 | phase-6 |
| **linting** | コード品質・スタイル | errors≤0, warnings≤10 | 全て |
| **security** | 脆弱性スキャン | critical≤0, high≤0 | phase-4+ |
| **tdd** | テスト駆動開発 | ratio≥1.2, compliance≥100% | phase-3+ |
| **visual** | ビジュアル回帰 | pixelDiff≤0.02 | phase-6 |
| **policy** | OPA準拠 | violations≤0 | phase-6 |
| **mutation** | ミューテーションテスト | score≥70% | phase-4+ |

#### 環境オーバーライド

##### 開発環境
- 高速反復のための緩い閾値
- 厳格な強制の代わりに警告
- 一部ゲートの無効化（lighthouse、visual）

##### CI環境
- 標準強制レベル
- 適用可能な全ゲート有効
- 品質とビルド速度のバランス

##### 本番環境
- 最も厳格な閾値
- 重要な問題に対するゼロトレランス
- 強化されたセキュリティとパフォーマンス要件

### 使用方法

#### コマンドラインインターフェース

##### 基本使用法
```bash
# 現在のフェーズに適用可能な全品質ゲートを実行
pnpm run quality:gates

# 特定環境で実行
pnpm run quality:gates:dev
pnpm run quality:gates:prod

# 特定ゲートのみ実行
pnpm run quality:run:accessibility
pnpm run quality:run:coverage

# 包括的品質チェック実行
pnpm run quality:run:all
```

##### 高度な使用法
```bash
# カスタム環境とフェーズ
node scripts/run-quality-gates.cjs --env=production --phase=phase-6

# 特定ゲート組み合わせ
node scripts/run-quality-gates.cjs --gates=accessibility,coverage,lighthouse

# ヘルプとオプション
node scripts/run-quality-gates.cjs --help
```

#### TypeScript統合

```text
import { 
  loadQualityPolicy, 
  getQualityGate, 
  shouldEnforceGate,
  validateQualityResults 
} from '../src/utils/quality-policy-loader.js';

// 環境オーバーライドでポリシーをロード
const policy = loadQualityPolicy('ci');

// 特定ゲート設定を取得
const accessibilityGate = getQualityGate('accessibility', 'ci');

// ゲートが強制されるべきかチェック
const shouldCheck = shouldEnforceGate('accessibility', 'phase-6', 'ci');

// 閾値に対して結果を検証
const validation = validateQualityResults('accessibility', {
  critical: 0,
  serious: 1,
  moderate: 2
}, 'ci');
```

#### GitHub Actions統合

システムはGitHub Actionsと自動的に統合されます：

```yaml
# 集約品質ゲートワークフローを使用
name: Quality Check
on: [push, pull_request]

jobs:
  quality:
    uses: ./.github/workflows/quality-gates-centralized.yml
    with:
      environment: 'ci'
      phase: 'auto-detect'
      gates: 'all'
```

### 実装詳細

#### ポリシーロードとオーバーライド

ポリシーローダーはドット記法パスシステムを使用して環境固有のオーバーライドを適用します：

```text
{
  "environments": {
    "development": {
      "overrides": {
        "accessibility.thresholds.total_warnings": 10,
        "coverage.enforcement": "warn"
      }
    }
  }
}
```

#### フェーズ認識強制

品質ゲートは以下のように設定できます：
1. 特定フェーズに適用: `"phases": ["phase-6"]`
2. 特定フェーズから有効化: `"enabledFromPhase": "phase-3"`
3. フェーズ制限が定義されていない場合は常に適用

#### ツール統合

##### Lighthouse CI
- ポリシー閾値に基づく動的設定
- 環境認識アサーションレベル
- 自動スコア変換（90 → 0.9）

##### カバレッジツール
- nycとvitestカバレッジの両方をサポート
- 設定可能な除外パターン
- 複数のメトリクスタイプ（行、関数、ブランチ、ステートメント）

##### アクセシビリティテスト
- jest-axeとaxe-coreとの統合
- 多レベル違反追跡
- 詳細な失敗レポート

#### エラーハンドリングとフォールバック

システムは堅牢なエラーハンドリングを含みます：

1. **ポリシーロード失敗**: CLIアーギュメントまたはデフォルトにフォールバック
2. **ツール利用不可**: 警告付きで欠落ツールのゲートをスキップ
3. **レポート生成**: 開発環境で空レポートを作成
4. **環境検出**: NODE_ENVから環境を自動検出

### カスタマイズ

#### 新しい品質ゲートの追加

1. **ポリシー設定の更新**:
```text
{
  "quality": {
    "myCustomGate": {
      "description": "カスタム品質ゲート",
      "enforcement": "strict",
      "thresholds": {
        "customMetric": 90
      },
      "tools": ["custom-tool"],
      "phases": ["phase-4", "phase-5", "phase-6"]
    }
  }
}
```

2. **ゲートランナーの実装**:
```text
// scripts/run-quality-gates.cjs内で
case 'myCustomGate':
  command = 'pnpm run <your-custom-check>'; // user-defined example
  break;
```

3. **NPMスクリプトの追加**:
```text
{
  "scripts": {
    "quality:custom": "node scripts/run-quality-gates.cjs --gates=myCustomGate"
  }
}
```

#### 閾値の変更

単純に`policy/quality.json`ファイルを更新：

```text
{
  "quality": {
    "coverage": {
      "thresholds": {
        "lines": 85,        // 80から変更
        "functions": 85     // 80から変更
      }
    }
  }
}
```

全てのツールとワークフローが自動的に新しい閾値を使用します。

#### 環境固有の調整

環境オーバーライドを追加または変更：

```text
{
  "environments": {
    "staging": {
      "description": "ステージング環境",
      "overrides": {
        "lighthouse.thresholds.performance": 85,
        "accessibility.enforcement": "warn"
      }
    }
  }
}
```

### ベストプラクティス

#### ポリシー管理
1. **バージョン管理**: ポリシーファイルを常にバージョン管理
2. **変更レビュー**: 閾値変更に承認を必要とする
3. **文書化**: 閾値の値の根拠を文書化
4. **段階的変更**: 閾値の増加を段階的に実装

#### 開発ワークフロー
1. **プレコミット**: コミット前に品質ゲートを実行
2. **ローカルテスト**: 反復に開発環境を使用
3. **フェーズ認識**: 現在のフェーズに適用されるゲートを理解
4. **継続監視**: 定期的な品質ゲート実行

#### CI/CD統合
1. **マトリックス戦略**: 高速フィードバックのための並列実行
2. **アーティファクト収集**: 分析のためレポートを保存
3. **失敗処理**: 適切なfail-fast vs. continue-on-error
4. **PRコメント**: プルリクエストでの自動フィードバック

### トラブルシューティング

#### 一般的な問題

##### ポリシーロード失敗
```bash
⚠️  Could not load quality policy: ENOENT: no such file or directory
```
**解決方法**: `policy/quality.json`が存在し、有効なJSONであることを確認。

##### フェーズ検出問題
```bash
⚠️  Could not detect current phase, using phase-1
```
**解決方法**: `.ae/phase-state.json`を作成するか、フェーズを明示的に指定：
```bash
node scripts/run-quality-gates.cjs --phase=phase-6
```

##### ツール利用不可
```bash
⚠️  Lighthouse CI config not found, skipping
```
**解決方法**: 必要なツールをインストールするか、ゲートをオプションとして設定。

#### デバッグモード

トラブルシューティングのために詳細ログを有効化：

```bash
DEBUG=quality-gates node scripts/run-quality-gates.cjs --env=development
```

#### 手動閾値検証

完全な品質ゲートを実行せずに特定の閾値をテスト：

```bash
# アクセシビリティのみチェック
node scripts/check-a11y-threshold.cjs --env=development

# カバレッジのみチェック
node scripts/check-coverage-threshold.cjs --env=ci
```

### マイグレーションガイド

#### ハードコード閾値から

1. **現在の閾値を特定**: 既存のスクリプトとワークフローをレビュー
2. **ポリシーファイルを更新**: `policy/quality.json`に現在の値を追加
3. **スクリプトを更新**: 集約ポリシーローダーを使用するように変更
4. **マイグレーションをテスト**: 新しいシステムで同じ動作を検証
5. **クリーンアップ**: スクリプトからハードコード値を削除

#### 複数設定ファイルから

1. **設定を統合**: 閾値を単一ポリシーにマージ
2. **ツール設定を更新**: 集約ポリシーから読み込むようにツールを変更
3. **環境マッピング**: 既存の環境固有設定をマップ
4. **検証**: 全てのシナリオが正常に動作することを確認

### 高度な機能

#### 条件付き強制

ゲートは以下に基づいて条件付きで強制できます：
- ファイル変更（GitHub Actionsパスフィルター経由）
- 環境変数
- 開発フェーズの進行
- カスタムビジネスロジック

#### レポート統合

システムは複数のレポート形式をサポート：
- プログラマティック消費用JSON
- 人間可読レポート用HTML
- CI/CD統合用JUnit XML
- プラグイン経由のカスタム形式

#### 通知システム

以下の通知を設定：
- 品質ゲート失敗
- 承認が必要な閾値変更
- トレンド分析と劣化アラート

この集約品質ゲートシステムは、AE-Framework開発ライフサイクル全体を通じて一貫したコード品質を維持するための堅牢な基盤を提供します。

#### current repository baseline との関係

現在の日常的な PR 運用では、required check の中心は以下です。

- `verify-lite`
- `policy-gate`
- `gate`

この文書が扱う集約品質ゲートは、`quality:gates` 互換エントリポイント、ローカル実行、条件付きワークフロー、および閾値ポリシーの中心として引き続き有効です。ただし、`quality-gates-centralized.yml` だけが現行の required baseline である、という意味ではありません。
