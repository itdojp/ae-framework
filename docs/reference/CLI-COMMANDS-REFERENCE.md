# AE Framework CLI Commands Reference

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

**Complete command-line interface reference for ae-framework's 6-phase software development workflow**

### 📋 Overview

The ae-framework CLI commands support the complete 6-phase software development workflow. Alongside Claude Code Task Tool integration, it provides a command-line environment for developers.

### Basic Syntax

```bash
ae-framework <command> [options] [flags]
```

## Common Options

### Global Flags
```bash
--help, -h          # Display help
--version, -v       # Display version
--config <path>     # Configuration file path
--verbose           # Detailed output
--quiet             # Minimal output
--sources <paths>   # Source file specification (comma-separated)
```

### Output Control
```bash
--format <format>   # Output format: json, yaml, table, markdown
--output <file>     # Output file specification
--no-color          # Disable color output
```

## Phase 1: Intent Analysis

### intent command
Execute requirements and intent analysis

```bash
# Basic requirements analysis
ae-framework intent --analyze --sources="requirements.md"

# Completeness validation
ae-framework intent --validate

# Analyze specific source files
ae-framework intent --analyze --sources="docs/requirements.md,specs/features.md"

# Output in JSON format
ae-framework intent --analyze --format=json --output=intent-analysis.json
```

**Options:**
- `--analyze`: Execute requirements analysis and intent extraction
- `--validate`: Validate Intent completeness
- `--sources <paths>`: Requirements source files (comma-separated)

**Example Output:**
```
✅ Intent Analysis Complete - 12 requirements identified
📋 Next steps:
  • Proceed to Phase 2 (Natural Language Requirements)
  • Review extracted requirements for completeness
  • Validate stakeholder understanding
```

## Phase 2: Natural Language Requirements

### natural-language command
Structure and analyze natural language requirements

```bash
# Requirements analysis
ae-framework natural-language --analyze --sources="requirements.md"

# Business entity extraction
ae-framework natural-language --extract-entities --sources="domain-docs.md"

# Completeness validation
ae-framework natural-language --validate-completeness --sources="all-requirements.md"

# Ambiguity resolution
ae-framework natural-language --resolve-ambiguity --sources="unclear-requirements.md"

# Requirements structuring
ae-framework natural-language --structure --sources="raw-requirements.md"

# Gap identification
ae-framework natural-language --identify-gaps --sources="current-requirements.md"
```

**Options:**
- `--analyze`: Analyze natural language requirements
- `--extract-entities`: Extract business entities
- `--validate-completeness`: Validate requirements completeness
- `--resolve-ambiguity`: Identify and propose ambiguity resolution
- `--structure`: Structure and classify requirements
- `--identify-gaps`: Identify requirements gaps

**Example Output:**
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

### cegis command
Automatic code repair using Counter-Example Guided Inductive Synthesis

```bash
# Basic repair execution
ae-framework cegis fix --files src/ --patterns="*.ts,*.js"

# Violation analysis
ae-framework cegis analyze --violations violations.json

# Generate repair candidates
ae-framework cegis generate-candidates --violations violations.json --max-candidates 5

# System status check
ae-framework cegis status

# Display repair history
ae-framework cegis history --limit 10

# Repair statistics
ae-framework cegis stats --format table
```

**Options:**
- `--files <paths>`: Target files/directories
- `--patterns <patterns>`: File patterns (comma-separated)
- `--violations <file>`: Violation definition file
- `--max-candidates <n>`: Maximum number of repair candidates
- `--timeout <ms>`: Repair timeout
- `--verify-fix`: Execute verification after repair

**Example Output:**
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

### conformance command
Real-time conformance verification system

```bash
# Basic verification execution
ae-framework conformance verify --rules rules.json

# Collect and display metrics
ae-framework conformance metrics --format json --output metrics.json

# Rule management
ae-framework conformance rules --list
ae-framework conformance rules --validate rules.json --output validation-report.json

# System configuration
ae-framework conformance config --show
ae-framework conformance config --create-sample --output sample-config.json

# System status monitoring
ae-framework conformance status --detailed

# Sample generation
ae-framework conformance sample --rules --output sample-rules.json
```

**Options:**
- `--rules <file>`: Rule definition file
- `--config <file>`: Configuration file
- `--output-dir <dir>`: Output directory
- `--collect-metrics`: Enable metrics collection
- `--sample-rate <rate>`: Sampling rate (0.0-1.0)
- `--timeout <ms>`: Execution timeout
- `--live`: Real-time monitoring mode

**Example Output:**
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

### integration command
Comprehensive integration testing and end-to-end test orchestration

```bash
# Test execution
ae-framework integration run --suites test-suites.json --environment test
ae-framework integration run --tests tests.json --parallel --max-concurrency 4

# Test discovery
ae-framework integration discover --patterns "./tests/**/*.json" --type all
ae-framework integration discover --patterns "./e2e/**/*.json" --type tests --output discovered-tests.json

# Resource listing
ae-framework integration list --type environments
ae-framework integration list --type runners --format table

# Sample generation
ae-framework integration generate --type test --test-type e2e --name "Login Test" --output login-test.json
ae-framework integration generate --type suite --name "Auth Suite" --output auth-suite.json

# System status monitoring
ae-framework integration status --watch --refresh 5

# Report management
ae-framework integration reports --list
ae-framework integration reports --clean --days 7
```

**Options:**
- `--tests <files>`: Test files (comma-separated)
- `--suites <files>`: Suite files (comma-separated)
- `--environment <name>`: Execution environment name
- `--categories <list>`: Category filter
- `--tags <list>`: Tag filter
- `--parallel`: Enable parallel execution
- `--max-concurrency <n>`: Maximum concurrency
- `--timeout <ms>`: Execution timeout
- `--output-dir <dir>`: Result output directory
- `--report-format <format>`: Report format (json,html)

**Example Output:**
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

### user-stories command
Generate and manage user stories

```bash
# Generate user stories
ae-framework user-stories --generate --sources="requirements.md"

# Validate stories
ae-framework user-stories --validate --sources="user-stories.md"

# Prioritization
ae-framework user-stories --prioritize --sources="backlog.md"

# Estimation
ae-framework user-stories --estimate --sources="sprint-stories.md"

# Create acceptance criteria
ae-framework user-stories --acceptance-criteria --sources="story-us001.md"

# Organize epics
ae-framework user-stories --organize-epics --sources="all-stories.md"

# Identify dependencies
ae-framework user-stories --dependencies --sources="release-stories.md"
```

**Options:**
- `--generate`: Generate user stories from requirements
- `--validate`: Validate story quality
- `--prioritize`: Prioritize by business value
- `--estimate`: Story point estimation
- `--acceptance-criteria`: Create acceptance criteria
- `--organize-epics`: Organize by epic
- `--dependencies`: Identify story dependencies

**Example Output:**
```
✅ User Story Generation Complete - 8 stories created across 3 epics
📊 Analysis:
  • Total Stories: 8
  • Total Epics: 3
  • Total Story Points: 34
  • Completeness Score: 85%
```

## Phase 4: Validation

### validate command
Quality verification of requirements, stories, and specifications

```bash
# Requirements validation
ae-framework validate --requirements --sources="requirements.md"

# User story validation
ae-framework validate --stories --sources="user-stories.md"

# Specification validation
ae-framework validate --specifications --sources="specs/"

# Traceability validation
ae-framework validate --traceability --sources="project/"

# Completeness validation
ae-framework validate --completeness --sources="all-artifacts/"

# Consistency validation
ae-framework validate --consistency --sources="documentation/"

# Feasibility validation
ae-framework validate --feasibility --sources="technical-specs/"

# Cross validation (all phases)
ae-framework validate --cross-validate --sources="complete-project/"
```

**Options:**
- `--requirements`: Validate requirements completeness and consistency
- `--stories`: Validate user story quality
- `--specifications`: Validate specification alignment
- `--traceability`: Validate traceability from requirements to code
- `--completeness`: Validate completeness across all phases
- `--consistency`: Validate consistency between phases
- `--feasibility`: Assess feasibility
- `--cross-validate`: Comprehensive validation across multiple phases

**Example Output:**
```
✅ Cross-Validation Complete - 90% alignment across phases
📊 Analysis:
  • Requirements-Stories alignment: 95%
  • Traceability coverage: 88%
  • Consistency score: 92%
```

## Phase 5: Domain Modeling

### domain-model command
Domain-driven design modeling

```bash
# Domain analysis
ae-framework domain-model --analyze --sources="requirements.md,user-stories.md"

# Entity identification
ae-framework domain-model --entities --sources="domain-requirements.md"

# Aggregate modeling
ae-framework domain-model --aggregates --sources="entities.md"

# Bounded context definition
ae-framework domain-model --contexts --sources="domain-analysis.md"

# Business rule extraction
ae-framework domain-model --rules --sources="business-requirements.md"

# Ubiquitous language creation
ae-framework domain-model --language --sources="domain-docs.md"

# Domain service design
ae-framework domain-model --services --sources="service-requirements.md"

# Model validation
ae-framework domain-model --validate --sources="complete-model.md"
```

**Options:**
- `--analyze`: Comprehensive domain analysis
- `--entities`: Identify and classify domain entities
- `--aggregates`: Design aggregates and boundary definitions
- `--contexts`: Define bounded contexts
- `--rules`: Extract business rules
- `--language`: Create ubiquitous language
- `--services`: Design domain services
- `--validate`: Validate domain model consistency

**Example Output:**
```
✅ Domain Analysis Complete - 6 entities, 2 bounded contexts identified
📊 Analysis:
  • Core Domain Entities: 4
  • Bounded Contexts: 2
  • Business Rules: 12
  • Domain Services: 3
```

## Phase Management Commands

### check command
Check current phase requirements

```bash
# Check current phase
ae-framework check

# Check specific phase
ae-framework check --phase 2-natural-language

# Check all phases status
ae-framework check --all

# Detailed report output
ae-framework check --phase 3-user-stories --verbose --output=phase3-report.md
```

### next command
Transition to next phase

```bash
# Prepare for next phase transition
ae-framework next

# Force next phase transition
ae-framework next --force

# Detailed pre-transition check
ae-framework next --validate --verbose
```

### guard command
Execute guards (quality gates)

```bash
# Execute all guards
ae-framework guard

# Execute specific guard
ae-framework guard --name "TDD Guard"

# Execute TDD-related guards
ae-framework guard --type tdd

# Execute custom guards
ae-framework guard --config custom-guards.yaml
```

### tdd command
TDD cycle verification

```bash
# Verify entire TDD cycle
ae-framework tdd

# Check RED-GREEN-REFACTOR cycle
ae-framework tdd --cycle

# Check test coverage
ae-framework tdd --coverage

# TDD violation report
ae-framework tdd --violations --output=tdd-report.json
```

## Utility Commands

### status command
Overall project status

```bash
# Overall status
ae-framework status

# Detailed status by phase
ae-framework status --detailed

# Display metrics
ae-framework status --metrics

# Output in JSON format
ae-framework status --format=json
```

### init command
Project initialization

```bash
# Basic initialization
ae-framework init my-project

# Initialize with TDD enforcement mode
ae-framework init my-project --tdd

# Specify template
ae-framework init my-project --template=microservice

# Generate configuration file only
ae-framework init --config-only
```

### config command
Configuration management

```bash
# Display current configuration
ae-framework config show

# Change configuration value
ae-framework config set tdd.enforcement true

# Validate configuration file
ae-framework config validate

# Restore default configuration
ae-framework config reset
```

## Advanced Usage Examples

### Pipeline Integration
```bash
# Usage in CI/CD pipeline
ae-framework check --phase current --format=json | jq '.success'
ae-framework validate --all --output=validation-report.xml --format=junit
ae-framework tdd --coverage --min-threshold=80
```

### Batch Processing
```bash
# Sequential execution of multiple commands
ae-framework intent --analyze && \
ae-framework natural-language --structure && \
ae-framework user-stories --generate && \
ae-framework validate --cross-validate
```

### Report Generation
```bash
# Comprehensive project reporting
ae-framework status --detailed --format=markdown > project-status.md
ae-framework validate --all --format=html > validation-report.html
ae-framework tdd --violations --format=csv > tdd-violations.csv
```

### Configuration File Example

#### .ae-framework.yaml
```yaml
# ae-framework configuration file
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

## Troubleshooting

### Common Errors and Solutions

**Error: Phase validation failed**
```bash
# Check detailed error information
ae-framework check --phase current --verbose

# Re-verify requirements
ae-framework validate --requirements --sources="requirements.md"
```

**Error: TDD Guard failed**
```bash
# Check detailed TDD violations
ae-framework tdd --violations

# Check test file existence
ae-framework guard --name "TDD Guard" --verbose
```

**Error: Source files not found**
```bash
# Check file paths
ls -la requirements.md user-stories.md

# Use relative paths
ae-framework intent --analyze --sources="./docs/requirements.md"
```

### Debug Options
```bash
# Execute in debug mode
DEBUG=ae-framework:* ae-framework intent --analyze

# Set log level
ae-framework --log-level=debug check --phase current

# Detailed output
ae-framework --verbose --no-color intent --analyze > debug.log 2>&1
```

---

## Japanese

**ae-frameworkの6フェーズソフトウェア開発ワークフローの完全なコマンドラインインターフェースリファレンス**

### 📋 概要

ae-frameworkのCLIコマンドは、全6フェーズにわたるソフトウェア開発ワークフローをサポートします。Claude Code Task Tool統合と並行して、開発者向けのコマンドライン環境を提供します。

### 基本構文

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

[Japanese content continues with all remaining sections...]

---

**🚀 Master efficient development with ae-framework CLI! / ae-framework CLIで効率的な開発をマスターしましょう！**