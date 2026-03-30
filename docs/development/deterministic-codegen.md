---
docRole: ssot
lastVerified: '2026-03-31'
owner: development-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Deterministic Code Generation & Drift Detection

> 🌍 Language / 言語: English | 日本語

---

## English

### Overview
The AE-Framework includes a deterministic code generation system that keeps code output stable for the same AE-IR input and detects drift when generated code diverges from the expected state.

### System scope
The system consists of:
- Deterministic code generator for AE-IR based outputs
- Drift detection engine for generated artifacts
- CI/CD integration for automated detection and regeneration
- Local CLI commands and helper scripts for development workflows

### Key features
#### Deterministic generation
- Consistent output from the same input
- SHA-256 hash based tracking for change detection
- Multi-target support for TypeScript, React, API, and database outputs
- Extensible template-based generation

#### Drift detection
- Detects specification changes in AE-IR inputs
- Identifies manual modifications to generated files
- Finds new, deleted, or renamed generated files
- Classifies drift by confidence and severity

#### Automation
- GitHub Actions based drift detection on PR and push flows
- Watch mode for local regeneration while editing specifications
- Quality gates for blocking critical drift
- Auto-fixing path for minor drift cases

### Architecture
#### Core components
```text
// Deterministic Code Generator
export class DeterministicCodeGenerator {
  async generate(): Promise<CodegenManifest>
  async detectDrift(): Promise<DriftDetectionResult>
}

// Drift Detection Engine
export class DriftDetector {
  async detectDrift(): Promise<DriftReport>
  private scanFileChanges(): Promise<FileChangeInfo[]>
}
```

#### Supported targets
| Target | Description | Generated Files |
|--------|-------------|-----------------|
| `typescript` | Type definitions and interfaces | `types/*.ts`, `schemas/*.ts` |
| `react` | React components and forms | `components/*.tsx` |
| `api` | API handlers and routes | `handlers/*.ts` |
| `database` | SQL schemas and ORM models | `migrations/*.sql`, `models/*.ts` |

### Usage
#### Command line interface
##### Basic code generation
```bash
# Generate TypeScript types
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/types -t typescript

# Generate React components
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/components -t react

# Generate API handlers
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/api -t api

# Generate database schemas
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/db -t database
```

##### Drift detection
```bash
# Check for drift in generated code
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json

# Detailed drift report
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --verbose

# JSON output for CI/CD
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --format json
```

##### Watch mode
```bash
# Watch for changes and auto-regenerate
pnpm ae-framework codegen watch -i .ae/ae-ir.json -o generated/types -t typescript
```

#### Scripts
```bash
# Generate all target types
pnpm codegen:generate

# Check drift across all targets
pnpm codegen:drift

# Regenerate only drifted code
pnpm codegen:regen

# Watch mode for development
pnpm codegen:watch

# Validate generated code
pnpm codegen:validate

# Show generation status
pnpm codegen:status

# Clean all generated code
pnpm codegen:clean
```

#### Helper script
The `scripts/codegen-tools.sh` helper supports batch operations.

```bash
# Generate all targets at once
./scripts/codegen-tools.sh generate-all

# Check drift across all generated code
./scripts/codegen-tools.sh check-drift

# Watch for changes and auto-regenerate
./scripts/codegen-tools.sh watch
```

### Configuration
#### Generation options
```text
interface CodegenOptions {
  inputPath: string;                    // AE-IR JSON file
  outputDir: string;                   // Output directory
  target: 'typescript' | 'react' | 'api' | 'database';
  templateDir?: string;                // Custom templates
  enableDriftDetection?: boolean;      // Enable drift detection (default: true)
  preserveManualChanges?: boolean;     // Preserve manual edits (default: true)
  hashAlgorithm?: 'sha256' | 'md5';    // Hash algorithm (default: sha256)
}
```

#### Drift detection config
```text
interface DriftConfig {
  codeDir: string;                     // Generated code directory
  specPath: string;                    // AE-IR specification file
  ignorePatterns?: string[];           // Files to ignore
  verbose?: boolean;                   // Detailed reporting
  autoFix?: boolean;                   // Auto-fix minor issues
}
```

### CI/CD integration
#### GitHub Actions workflow
The repository includes `.github/workflows/codegen-drift-check.yml` for:
1. Detecting drift from specification and generated code changes
2. Regenerating outdated code
3. Validating that generated output compiles and passes checks
4. Posting detailed drift reports to pull requests
5. Blocking merges when drift reaches critical severity

#### Workflow triggers
- Pushes to `main` that change specifications
- Pull requests that modify specifications
- Changes to the codegen system or templates

#### Exit codes
| Code | Status | Meaning |
|------|--------|---------|
| 0 | `no_drift` | No drift detected |
| 1 | `minor_drift` | Minor changes, regeneration recommended |
| 2 | `major_drift` | Major changes, regeneration required |
| 3 | `critical_drift` | Critical changes, immediate action required |

### Drift detection levels
#### No drift
- Generated code matches the specification exactly
- No manual modifications are detected
- All expected files are present and unchanged

#### Minor drift
- Small manual modifications exist in generated files
- Changes are non-critical and usually auto-fixable

#### Major drift
- Significant manual changes exist in generated files
- Multiple files are affected
- Regeneration is recommended before merging

#### Critical drift
- Specification changes are large or structural
- Many generated files were deleted or heavily modified
- Immediate regeneration is required

### Development workflow
#### 1. Specification changes
```bash
# Edit specification
vim spec/my-spec.md

# Compile to AE-IR
pnpm ae-framework spec compile -i spec/my-spec.md -o .ae/ae-ir.json

# Check what needs regeneration
pnpm codegen:drift

# Regenerate affected code
pnpm codegen:regen
```

#### 2. Local development
```bash
# Start watch mode for real-time updates
pnpm codegen:watch

# In another terminal, edit specifications
# Watch mode will automatically regenerate code
```

#### 3. Pre-commit validation
```bash
# Before committing, check for drift
pnpm codegen:drift

# Validate generated code compiles
pnpm codegen:validate

# Check generation status
pnpm codegen:status
```

### Generated file structure
#### TypeScript target
```text
generated/typescript/
├── .codegen-manifest.json
├── types/
│   └── domain.ts
├── schemas/
│   └── validation.ts
└── api.ts
```

#### React target
```text
generated/react/
├── .codegen-manifest.json
├── components/
│   ├── UserForm.tsx
│   ├── UserList.tsx
│   ├── ProductForm.tsx
│   └── ProductList.tsx
```

#### API target
```text
generated/api/
├── .codegen-manifest.json
└── handlers/
    ├── users_get.ts
    ├── users_post.ts
    └── products_get.ts
```

#### Database target
```text
generated/database/
├── .codegen-manifest.json
├── migrations/
│   └── 001_initial_schema.sql
└── models/
    ├── User.ts
    └── Product.ts
```

### Manifest file format
Each generated directory contains a `.codegen-manifest.json` file.

```text
{
  "metadata": {
    "generatedAt": "2025-01-20T10:00:00Z",
    "specHash": "sha256:abc123...",
    "templateHash": "sha256:def456...",
    "options": { /* generation options */ }
  },
  "files": [
    {
      "filePath": "types/domain.ts",
      "content": "...",
      "hash": "sha256:...",
      "timestamp": "2025-01-20T10:00:00Z",
      "specHash": "sha256:..."
    }
  ]
}
```

### Best practices
#### Specification management
- Keep AE-IR files in version control
- Use descriptive commit messages when updating specs
- Tag specification versions for release management

#### Generated code handling
- Do not manually edit generated files
- Add `// DO NOT MODIFY` headers to generated files
- Use `.gitignore` for generated directories when they are not committed

#### Drift management
- Run drift detection regularly during development
- Address drift promptly to avoid accumulation
- Use CI/CD quality gates to block drift from reaching production

#### Template customization
- Create organization-specific templates
- Keep template files in version control
- Test template changes against existing specifications

### Troubleshooting
#### Common issues
##### No AE-IR file found
```bash
# Solution: compile the specification first
pnpm ae-framework spec compile -i spec/my-spec.md -o .ae/ae-ir.json
```

##### Drift detection failed
```bash
# Solution: verify that the manifest exists
ls generated/*/.codegen-manifest.json

# Regenerate if the manifest is missing
pnpm codegen:generate
```

##### Generated code does not compile
```bash
# Solution: validate and regenerate
pnpm codegen:validate
pnpm codegen:regen
```

#### Debug mode
```bash
# Verbose drift detection
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --verbose

# Verbose generation
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/types -t typescript --verbose
```

#### Manual recovery
```bash
# Clean all generated code
pnpm codegen:clean

# Regenerate everything from scratch
pnpm codegen:generate

# Verify status
pnpm codegen:status
```

### Integration with other systems
#### Spec compiler integration
```bash
# Compile spec and generate code in one workflow
pnpm ae-framework spec compile -i spec/my-spec.md -o .ae/ae-ir.json
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/types -t typescript
```

#### Build system integration
```text
{
  "scripts": {
    "prebuild": "pnpm codegen:drift && pnpm codegen:validate",
    "build": "tsc",
    "postbuild": "pnpm codegen:status"
  }
}
```

### Metrics and monitoring
The system tracks:
- Generation success and failure rates
- Drift detection frequency and severity
- Code validation results
- Performance metrics such as generation time and file counts

Access metrics through:
- GitHub Actions artifacts
- CI/CD dashboard integration
- Local status reports

The deterministic code generation system is intended to keep generated code consistent, up to date, and reliable throughout the development lifecycle.

## 日本語

### 概要
AE-Framework には、同一の AE-IR 入力に対して安定した code output を維持し、生成済み code が期待状態から逸脱した場合に drift を検出する deterministic code generation system が含まれます。

### システム範囲
この system は次の要素で構成されます。
- AE-IR ベースの出力を生成する deterministic code generator
- 生成 artifact の drift を検出する drift detection engine
- 検出と再生成を自動化する CI/CD integration
- local 開発 workflow 向けの CLI command と helper script

### 主な機能
#### Deterministic generation
- 同一入力から一貫した output を生成する
- SHA-256 hash による change detection を行う
- TypeScript、React、API、database 出力を対象にした multi-target support
- 拡張可能な template-based generation

#### Drift detection
- AE-IR specification の変更を検出する
- 生成 file に対する manual modification を特定する
- 新規、削除、rename された generated file を検出する
- confidence と severity に基づいて drift を分類する

#### Automation
- PR / push flow 上で GitHub Actions により drift を検出する
- specification 編集中の local regeneration 用 watch mode を提供する
- critical drift を block する quality gate を提供する
- minor drift 向けの auto-fix path を提供する

### アーキテクチャ
#### Core component
```text
// Deterministic Code Generator
export class DeterministicCodeGenerator {
  async generate(): Promise<CodegenManifest>
  async detectDrift(): Promise<DriftDetectionResult>
}

// Drift Detection Engine
export class DriftDetector {
  async detectDrift(): Promise<DriftReport>
  private scanFileChanges(): Promise<FileChangeInfo[]>
}
```

#### 対応 target
| Target | 説明 | 生成される file |
|--------|------|-----------------|
| `typescript` | 型定義と interface | `types/*.ts`, `schemas/*.ts` |
| `react` | React component と form | `components/*.tsx` |
| `api` | API handler と route | `handlers/*.ts` |
| `database` | SQL schema と ORM model | `migrations/*.sql`, `models/*.ts` |

### 使い方
#### Command line interface
##### 基本的な code generation
```bash
# TypeScript types を生成
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/types -t typescript

# React components を生成
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/components -t react

# API handlers を生成
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/api -t api

# Database schemas を生成
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/db -t database
```

##### Drift detection
```bash
# generated code の drift を確認
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json

# 詳細な drift report
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --verbose

# CI/CD 向け JSON 出力
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --format json
```

##### Watch mode
```bash
# change を watch して自動再生成
pnpm ae-framework codegen watch -i .ae/ae-ir.json -o generated/types -t typescript
```

#### Script
```bash
# すべての target を生成
pnpm codegen:generate

# 全 target の drift を確認
pnpm codegen:drift

# drift した code のみ再生成
pnpm codegen:regen

# 開発用 watch mode
pnpm codegen:watch

# generated code を検証
pnpm codegen:validate

# generation status を表示
pnpm codegen:status

# generated code を全削除
pnpm codegen:clean
```

#### Helper script
`scripts/codegen-tools.sh` は batch operation を補助します。

```bash
# 全 target を一括生成
./scripts/codegen-tools.sh generate-all

# 全 generated code の drift を確認
./scripts/codegen-tools.sh check-drift

# change を watch して自動再生成
./scripts/codegen-tools.sh watch
```

### 設定
#### Generation option
```text
interface CodegenOptions {
  inputPath: string;                    // AE-IR JSON file
  outputDir: string;                   // Output directory
  target: 'typescript' | 'react' | 'api' | 'database';
  templateDir?: string;                // Custom templates
  enableDriftDetection?: boolean;      // Enable drift detection (default: true)
  preserveManualChanges?: boolean;     // Preserve manual edits (default: true)
  hashAlgorithm?: 'sha256' | 'md5';    // Hash algorithm (default: sha256)
}
```

#### Drift detection config
```text
interface DriftConfig {
  codeDir: string;                     // Generated code directory
  specPath: string;                    // AE-IR specification file
  ignorePatterns?: string[];           // Files to ignore
  verbose?: boolean;                   // Detailed reporting
  autoFix?: boolean;                   // Auto-fix minor issues
}
```

### CI/CD integration
#### GitHub Actions workflow
repository には `.github/workflows/codegen-drift-check.yml` が含まれており、次を実行します。
1. specification と generated code の変更から drift を検出する
2. outdated code を再生成する
3. generated output が compile / check を通ることを検証する
4. pull request に詳細な drift report を投稿する
5. drift が critical severity の場合は merge を block する

#### Workflow trigger
- specification change を含む `main` への push
- specification を変更する pull request
- codegen system または template の変更

#### Exit code
| Code | Status | 意味 |
|------|--------|------|
| 0 | `no_drift` | drift なし |
| 1 | `minor_drift` | 軽微な変更。再生成推奨 |
| 2 | `major_drift` | 大きな変更。再生成必須 |
| 3 | `critical_drift` | 重大な変更。即時対応が必要 |

### Drift detection level
#### No drift
- generated code が specification と完全一致する
- manual modification が検出されない
- 想定 file がすべて存在し未変更である

#### Minor drift
- generated file に軽微な manual modification がある
- non-critical な change で、多くは auto-fix 可能

#### Major drift
- generated file に大きな manual change がある
- 複数 file が影響を受けている
- merge 前に再生成することが推奨される

#### Critical drift
- specification change が大きい、または構造的である
- 多数の generated file が削除または大幅変更されている
- 即時再生成が必要である

### 開発 workflow
#### 1. Specification change
```bash
# specification を編集
vim spec/my-spec.md

# AE-IR に compile
pnpm ae-framework spec compile -i spec/my-spec.md -o .ae/ae-ir.json

# 再生成が必要な対象を確認
pnpm codegen:drift

# 影響範囲を再生成
pnpm codegen:regen
```

#### 2. Local development
```bash
# watch mode を開始
pnpm codegen:watch

# 別 terminal で specification を編集
# watch mode が自動再生成する
```

#### 3. Pre-commit validation
```bash
# commit 前に drift を確認
pnpm codegen:drift

# generated code が compile するか確認
pnpm codegen:validate

# generation status を確認
pnpm codegen:status
```

### 生成 file 構造
#### TypeScript target
```text
generated/typescript/
├── .codegen-manifest.json
├── types/
│   └── domain.ts
├── schemas/
│   └── validation.ts
└── api.ts
```

#### React target
```text
generated/react/
├── .codegen-manifest.json
├── components/
│   ├── UserForm.tsx
│   ├── UserList.tsx
│   ├── ProductForm.tsx
│   └── ProductList.tsx
```

#### API target
```text
generated/api/
├── .codegen-manifest.json
└── handlers/
    ├── users_get.ts
    ├── users_post.ts
    └── products_get.ts
```

#### Database target
```text
generated/database/
├── .codegen-manifest.json
├── migrations/
│   └── 001_initial_schema.sql
└── models/
    ├── User.ts
    └── Product.ts
```

### Manifest file format
各 generated directory には `.codegen-manifest.json` が含まれます。

```text
{
  "metadata": {
    "generatedAt": "2025-01-20T10:00:00Z",
    "specHash": "sha256:abc123...",
    "templateHash": "sha256:def456...",
    "options": { /* generation options */ }
  },
  "files": [
    {
      "filePath": "types/domain.ts",
      "content": "...",
      "hash": "sha256:...",
      "timestamp": "2025-01-20T10:00:00Z",
      "specHash": "sha256:..."
    }
  ]
}
```

### ベストプラクティス
#### Specification management
- AE-IR file を version control に含める
- specification 更新時は説明的な commit message を使う
- release 管理用に specification version を tag する

#### Generated code handling
- generated file を手動編集しない
- generated file に `// DO NOT MODIFY` header を追加する
- commit しない generated directory には `.gitignore` を適用する

#### Drift management
- 開発中は定期的に drift detection を実行する
- drift は蓄積させずに早めに解消する
- CI/CD quality gate で production への drift 流入を防ぐ

#### Template customization
- 組織固有の template を作成する
- template file を version control に置く
- template change は既存 specification に対して検証する

### Troubleshooting
#### よくある問題
##### AE-IR file が見つからない
```bash
# Solution: 先に specification を compile する
pnpm ae-framework spec compile -i spec/my-spec.md -o .ae/ae-ir.json
```

##### Drift detection failed
```bash
# Solution: manifest の存在を確認する
ls generated/*/.codegen-manifest.json

# manifest が無ければ再生成
pnpm codegen:generate
```

##### Generated code does not compile
```bash
# Solution: validate と regenerate を実行
pnpm codegen:validate
pnpm codegen:regen
```

#### Debug mode
```bash
# Verbose drift detection
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --verbose

# Verbose generation
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/types -t typescript --verbose
```

#### Manual recovery
```bash
# generated code を全削除
pnpm codegen:clean

# すべて再生成
pnpm codegen:generate

# status を確認
pnpm codegen:status
```

### 他 system との統合
#### Spec compiler integration
```bash
# spec compile と code generation を連続実行
pnpm ae-framework spec compile -i spec/my-spec.md -o .ae/ae-ir.json
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/types -t typescript
```

#### Build system integration
```text
{
  "scripts": {
    "prebuild": "pnpm codegen:drift && pnpm codegen:validate",
    "build": "tsc",
    "postbuild": "pnpm codegen:status"
  }
}
```

### Metrics and monitoring
この system は次を追跡します。
- generation success / failure rate
- drift detection の頻度と severity
- code validation result
- generation time や file count などの performance metric

参照先:
- GitHub Actions artifact
- CI/CD dashboard integration
- local status report

deterministic code generation system は、開発 lifecycle 全体で generated code を一貫・最新・信頼可能な状態に維持することを目的とします。
