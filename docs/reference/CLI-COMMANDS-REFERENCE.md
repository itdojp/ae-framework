# CLI Commands Reference

## 概要

ae-frameworkのCLIコマンドは、全6フェーズにわたるソフトウェア開発ワークフローをサポートします。Claude Code Task Tool統合と並行して、開発者向けのコマンドライン環境を提供します。

## 基本構文

```bash
ae-framework <command> [options] [flags]
```

## 共通オプション

### グローバルフラグ
```bash
--help, -h          # ヘルプ表示
--version, -v       # バージョン表示
--config <path>     # 設定ファイルパス
--verbose           # 詳細出力
--quiet             # 最小出力
--sources <paths>   # ソースファイル指定（カンマ区切り）
```

### 出力制御
```bash
--format <format>   # 出力形式: json, yaml, table, markdown
--output <file>     # 出力ファイル指定
--no-color          # カラー出力無効化
```

## Phase 1: Intent Analysis

### intent コマンド
要件と意図の分析を実行

```bash
# 基本的な要件分析
ae-framework intent --analyze --sources="requirements.md"

# 完全性検証
ae-framework intent --validate

# 特定のソースファイルを分析
ae-framework intent --analyze --sources="docs/requirements.md,specs/features.md"

# JSON形式で出力
ae-framework intent --analyze --format=json --output=intent-analysis.json
```

**オプション:**
- `--analyze`: 要件分析と意図抽出を実行
- `--validate`: Intent完全性の検証
- `--sources <paths>`: 要件ソースファイル（カンマ区切り）

**出力例:**
```
✅ Intent Analysis Complete - 12 requirements identified
📋 Next steps:
  • Proceed to Phase 2 (Natural Language Requirements)
  • Review extracted requirements for completeness
  • Validate stakeholder understanding
```

## Phase 2: Natural Language Requirements

### natural-language コマンド
自然言語要件の構造化と分析

```bash
# 要件分析
ae-framework natural-language --analyze --sources="requirements.md"

# ビジネスエンティティ抽出
ae-framework natural-language --extract-entities --sources="domain-docs.md"

# 完全性検証
ae-framework natural-language --validate-completeness --sources="all-requirements.md"

# 曖昧性解決
ae-framework natural-language --resolve-ambiguity --sources="unclear-requirements.md"

# 要件構造化
ae-framework natural-language --structure --sources="raw-requirements.md"

# ギャップ識別
ae-framework natural-language --identify-gaps --sources="current-requirements.md"
```

**オプション:**
- `--analyze`: 自然言語要件の分析
- `--extract-entities`: ビジネスエンティティの抽出
- `--validate-completeness`: 要件完全性の検証
- `--resolve-ambiguity`: 曖昧性の識別と解決提案
- `--structure`: 要件の構造化と分類
- `--identify-gaps`: 要件ギャップの識別

**出力例:**
```
✅ Requirements Analysis - 15 requirements identified
📊 Analysis:
  • Functional Requirements: 10
  • Non-Functional Requirements: 3
  • Business Requirements: 2
💡 Recommendations:
  • Review identified gaps for completeness
  • Clarify ambiguous requirements with stakeholders
```

## Phase 2.1: CEGIS Auto-Fix System

### cegis コマンド
Counter-Example Guided Inductive Synthesis による自動コード修復

```bash
# 基本的な修復実行
ae-framework cegis fix --files src/ --patterns="*.ts,*.js"

# 違反分析
ae-framework cegis analyze --violations violations.json

# 修復候補生成
ae-framework cegis generate-candidates --violations violations.json --max-candidates 5

# システム状態確認
ae-framework cegis status

# 修復履歴表示
ae-framework cegis history --limit 10

# 修復統計
ae-framework cegis stats --format table
```

**オプション:**
- `--files <paths>`: 対象ファイル/ディレクトリ
- `--patterns <patterns>`: ファイルパターン（カンマ区切り）
- `--violations <file>`: 違反定義ファイル
- `--max-candidates <n>`: 修復候補の最大数
- `--timeout <ms>`: 修復タイムアウト
- `--verify-fix`: 修復後の検証実行

**出力例:**
```
🔧 CEGIS Auto-Fix System - Analyzing 15 files
📊 Analysis Results:
  • Violations Found: 8
  • Fix Candidates: 12
  • Successfully Applied: 7
  • Verification Passed: 6
💡 Recommendations:
  • Review remaining violation: src/utils/validation.ts:42
  • Manual intervention required for complex cases
```

## Phase 2.2: Runtime Conformance Verification

### conformance コマンド
リアルタイム適合性検証システム

```bash
# 基本的な検証実行
ae-framework conformance verify --rules rules.json

# メトリクス収集と表示
ae-framework conformance metrics --format json --output metrics.json

# 規則管理
ae-framework conformance rules --list
ae-framework conformance rules --validate rules.json --output validation-report.json

# システム設定
ae-framework conformance config --show
ae-framework conformance config --create-sample --output sample-config.json

# システム状態監視
ae-framework conformance status --detailed

# サンプル生成
ae-framework conformance sample --rules --output sample-rules.json
```

**オプション:**
- `--rules <file>`: 規則定義ファイル
- `--config <file>`: 設定ファイル
- `--output-dir <dir>`: 出力ディレクトリ
- `--collect-metrics`: メトリクス収集有効化
- `--sample-rate <rate>`: サンプリング率 (0.0-1.0)
- `--timeout <ms>`: 実行タイムアウト
- `--live`: リアルタイム監視モード

**出力例:**
```
🛡️ Runtime Conformance Verification - Processing 25 rules
📊 Verification Results:
  • Rules Executed: 25
  • Violations Detected: 3
  • Success Rate: 88%
  • Average Response Time: 245ms
⚠️  Violations:
  • API rate limit exceeded: /api/users (severity: major)
  • Data validation failed: user.email (severity: minor)
💡 Recommendations:
  • Implement rate limiting for /api/users endpoint
  • Add email validation in user input form
```

## Phase 2.3: Integration Testing System

### integration コマンド
包括的統合テストとエンドツーエンドテストのオーケストレーション

```bash
# テスト実行
ae-framework integration run --suites test-suites.json --environment test
ae-framework integration run --tests tests.json --parallel --max-concurrency 4

# テスト発見
ae-framework integration discover --patterns "./tests/**/*.json" --type all
ae-framework integration discover --patterns "./e2e/**/*.json" --type tests --output discovered-tests.json

# リソース一覧
ae-framework integration list --type environments
ae-framework integration list --type runners --format table

# サンプル生成
ae-framework integration generate --type test --test-type e2e --name "Login Test" --output login-test.json
ae-framework integration generate --type suite --name "Auth Suite" --output auth-suite.json

# システム状態監視
ae-framework integration status --watch --refresh 5

# レポート管理
ae-framework integration reports --list
ae-framework integration reports --clean --days 7
```

**オプション:**
- `--tests <files>`: テストファイル（カンマ区切り）
- `--suites <files>`: スイートファイル（カンマ区切り）
- `--environment <name>`: 実行環境名
- `--categories <list>`: カテゴリフィルター
- `--tags <list>`: タグフィルター
- `--parallel`: 並列実行有効化
- `--max-concurrency <n>`: 最大並行数
- `--timeout <ms>`: 実行タイムアウト
- `--output-dir <dir>`: 結果出力ディレクトリ
- `--report-format <format>`: レポート形式（json,html）

**出力例:**
```
🧪 Integration Testing System - Executing 12 test suites
📊 Execution Results:
  • Test Suites: 12 (8 passed, 4 failed)
  • Total Tests: 156 (142 passed, 14 failed)
  • Execution Time: 8min 32sec
  • Pass Rate: 91%
📋 Failed Tests:
  • auth-suite: Password reset functionality (timeout)
  • api-suite: Rate limiting validation (assertion failed)
💡 Recommendations:
  • Increase timeout for password reset tests
  • Review API rate limiting implementation
  • Generate detailed HTML report for stakeholder review
```

## Phase 3: User Stories Creation

### user-stories コマンド
ユーザーストーリーの生成と管理

```bash
# ユーザーストーリー生成
ae-framework user-stories --generate --sources="requirements.md"

# ストーリー検証
ae-framework user-stories --validate --sources="user-stories.md"

# 優先順位付け
ae-framework user-stories --prioritize --sources="backlog.md"

# 見積もり
ae-framework user-stories --estimate --sources="sprint-stories.md"

# 受入基準作成
ae-framework user-stories --acceptance-criteria --sources="story-us001.md"

# エピック組織化
ae-framework user-stories --organize-epics --sources="all-stories.md"

# 依存関係識別
ae-framework user-stories --dependencies --sources="release-stories.md"
```

**オプション:**
- `--generate`: 要件からユーザーストーリーを生成
- `--validate`: ストーリーの品質検証
- `--prioritize`: ビジネス価値による優先順位付け
- `--estimate`: ストーリーポイント見積もり
- `--acceptance-criteria`: 受入基準の作成
- `--organize-epics`: エピック単位での組織化
- `--dependencies`: ストーリー依存関係の識別

**出力例:**
```
✅ User Story Generation Complete - 8 stories created across 3 epics
📊 Analysis:
  • Total Stories: 8
  • Total Epics: 3
  • Total Story Points: 34
  • Completeness Score: 85%
```

## Phase 4: Validation

### validate コマンド
要件・ストーリー・仕様の品質検証

```bash
# 要件検証
ae-framework validate --requirements --sources="requirements.md"

# ユーザーストーリー検証
ae-framework validate --stories --sources="user-stories.md"

# 仕様検証
ae-framework validate --specifications --sources="specs/"

# トレーサビリティ検証
ae-framework validate --traceability --sources="project/"

# 完全性検証
ae-framework validate --completeness --sources="all-artifacts/"

# 一貫性検証
ae-framework validate --consistency --sources="documentation/"

# 実現可能性検証
ae-framework validate --feasibility --sources="technical-specs/"

# クロス検証（全フェーズ）
ae-framework validate --cross-validate --sources="complete-project/"
```

**オプション:**
- `--requirements`: 要件の完全性と一貫性検証
- `--stories`: ユーザーストーリーの品質検証
- `--specifications`: 仕様の整合性検証
- `--traceability`: 要件からコードまでの追跡可能性検証
- `--completeness`: 全フェーズの完全性検証
- `--consistency`: フェーズ間の一貫性検証
- `--feasibility`: 実現可能性評価
- `--cross-validate`: 複数フェーズにわたる総合検証

**出力例:**
```
✅ Cross-Validation Complete - 90% alignment across phases
📊 Analysis:
  • Requirements-Stories alignment: 95%
  • Traceability coverage: 88%
  • Consistency score: 92%
```

## Phase 5: Domain Modeling

### domain-model コマンド
ドメイン駆動設計によるモデリング

```bash
# ドメイン分析
ae-framework domain-model --analyze --sources="requirements.md,user-stories.md"

# エンティティ識別
ae-framework domain-model --entities --sources="domain-requirements.md"

# 集約モデリング
ae-framework domain-model --aggregates --sources="entities.md"

# 境界コンテキスト定義
ae-framework domain-model --contexts --sources="domain-analysis.md"

# ビジネスルール抽出
ae-framework domain-model --rules --sources="business-requirements.md"

# ユビキタス言語作成
ae-framework domain-model --language --sources="domain-docs.md"

# ドメインサービス設計
ae-framework domain-model --services --sources="service-requirements.md"

# モデル検証
ae-framework domain-model --validate --sources="complete-model.md"
```

**オプション:**
- `--analyze`: ドメインの包括的分析
- `--entities`: ドメインエンティティの識別と分類
- `--aggregates`: 集約の設計と境界定義
- `--contexts`: 境界コンテキストの定義
- `--rules`: ビジネスルールの抽出
- `--language`: ユビキタス言語の作成
- `--services`: ドメインサービスの設計
- `--validate`: ドメインモデルの整合性検証

**出力例:**
```
✅ Domain Analysis Complete - 6 entities, 2 bounded contexts identified
📊 Analysis:
  • Core Domain Entities: 4
  • Bounded Contexts: 2
  • Business Rules: 12
  • Domain Services: 3
```

## フェーズ管理コマンド

### check コマンド
現在フェーズの要件チェック

```bash
# 現在フェーズのチェック
ae-framework check

# 特定フェーズのチェック
ae-framework check --phase 2-natural-language

# 全フェーズのステータス確認
ae-framework check --all

# 詳細レポート出力
ae-framework check --phase 3-user-stories --verbose --output=phase3-report.md
```

### next コマンド
次フェーズへの移行

```bash
# 次フェーズへの移行準備
ae-framework next

# 強制的な次フェーズ移行
ae-framework next --force

# 移行前の詳細チェック
ae-framework next --validate --verbose
```

### guard コマンド
ガード（品質ゲート）の実行

```bash
# 全ガードの実行
ae-framework guard

# 特定ガードの実行
ae-framework guard --name "TDD Guard"

# TDD関連ガードの実行
ae-framework guard --type tdd

# カスタムガードの実行
ae-framework guard --config custom-guards.yaml
```

### tdd コマンド
TDDサイクル検証

```bash
# TDDサイクル全体の検証
ae-framework tdd

# RED-GREEN-REFACTORサイクルチェック
ae-framework tdd --cycle

# テストカバレッジ確認
ae-framework tdd --coverage

# TDD違反レポート
ae-framework tdd --violations --output=tdd-report.json
```

## ユーティリティコマンド

### status コマンド
プロジェクト全体のステータス

```bash
# 全体ステータス
ae-framework status

# フェーズ別詳細ステータス
ae-framework status --detailed

# メトリクス表示
ae-framework status --metrics

# JSON形式で出力
ae-framework status --format=json
```

### init コマンド
プロジェクト初期化

```bash
# 基本的な初期化
ae-framework init my-project

# TDD強制モードで初期化
ae-framework init my-project --tdd

# テンプレート指定
ae-framework init my-project --template=microservice

# 設定ファイル生成
ae-framework init --config-only
```

### config コマンド
設定管理

```bash
# 現在の設定表示
ae-framework config show

# 設定値の変更
ae-framework config set tdd.enforcement true

# 設定ファイルの検証
ae-framework config validate

# デフォルト設定の復元
ae-framework config reset
```

## 高度な使用例

### パイプライン統合
```bash
# CI/CDパイプラインでの使用
ae-framework check --phase current --format=json | jq '.success'
ae-framework validate --all --output=validation-report.xml --format=junit
ae-framework tdd --coverage --min-threshold=80
```

### バッチ処理
```bash
# 複数コマンドの連続実行
ae-framework intent --analyze && \
ae-framework natural-language --structure && \
ae-framework user-stories --generate && \
ae-framework validate --cross-validate
```

### レポート生成
```bash
# 包括的なプロジェクトレポート
ae-framework status --detailed --format=markdown > project-status.md
ae-framework validate --all --format=html > validation-report.html
ae-framework tdd --violations --format=csv > tdd-violations.csv
```

### 設定ファイル例

#### .ae-framework.yaml
```yaml
# ae-framework設定ファイル
project:
  name: "My Project"
  type: "web-application"

phases:
  intent:
    required_artifacts: ["requirements.md"]
    validation_rules: ["completeness", "clarity"]
  
  natural-language:
    completeness_threshold: 80
    ambiguity_tolerance: "low"
  
  user-stories:
    format_enforcement: true
    acceptance_criteria_required: true
  
  validation:
    cross_validation: true
    traceability_required: true
  
  domain-modeling:
    ddd_patterns: true
    bounded_context_enforcement: true

tdd:
  enforcement: true
  coverage_threshold: 80
  red_green_cycle: true

output:
  default_format: "table"
  verbose: false
  color: true
```

## トラブルシューティング

### よくあるエラーと解決策

**エラー: Phase validation failed**
```bash
# 詳細なエラー情報を確認
ae-framework check --phase current --verbose

# 要件を再確認
ae-framework validate --requirements --sources="requirements.md"
```

**エラー: TDD Guard failed**
```bash
# TDD違反の詳細確認
ae-framework tdd --violations

# テストファイルの存在確認
ae-framework guard --name "TDD Guard" --verbose
```

**エラー: Source files not found**
```bash
# ファイルパスの確認
ls -la requirements.md user-stories.md

# 相対パスの使用
ae-framework intent --analyze --sources="./docs/requirements.md"
```

### デバッグオプション
```bash
# デバッグモードでの実行
DEBUG=ae-framework:* ae-framework intent --analyze

# ログレベルの設定
ae-framework --log-level=debug check --phase current

# 詳細出力
ae-framework --verbose --no-color intent --analyze > debug.log 2>&1
```