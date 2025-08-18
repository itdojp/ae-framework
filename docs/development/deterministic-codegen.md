# Deterministic Code Generation & Drift Detection

The AE-Framework includes a comprehensive deterministic code generation system that ensures consistent code output from AE-IR specifications and detects when generated code drifts from its expected state.

## Overview

The system consists of:

- **Deterministic Code Generator**: Generates consistent code from AE-IR specifications
- **Drift Detection Engine**: Monitors changes and inconsistencies in generated code  
- **CI/CD Integration**: Automated drift detection and code regeneration
- **Development Tools**: CLI commands and helper scripts

## Key Features

### 🔄 Deterministic Generation
- **Consistent Output**: Same input always produces identical output
- **Hash-based Tracking**: SHA-256 hashes for change detection
- **Multi-target Support**: TypeScript, React, API, Database schemas
- **Template System**: Extensible template-based generation

### 🔍 Drift Detection  
- **Specification Changes**: Detects when source AE-IR changes
- **Manual Modifications**: Identifies developer changes to generated files
- **Structural Changes**: Finds new, deleted, or renamed files
- **Confidence Levels**: High/medium/low confidence drift classification

### ⚙️ Automation
- **GitHub Actions**: Automated drift detection on PR/push
- **Watch Mode**: Real-time regeneration on specification changes
- **Quality Gates**: Prevents deployment with critical drift
- **Auto-fixing**: Automatic resolution of minor drift issues

## Architecture

### Core Components

```typescript
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

### Supported Targets

| Target | Description | Generated Files |
|--------|-------------|-----------------|
| `typescript` | Type definitions and interfaces | `types/*.ts`, `schemas/*.ts` |
| `react` | React components and forms | `components/*.tsx` |
| `api` | API handlers and routes | `handlers/*.ts` |  
| `database` | SQL schemas and ORM models | `migrations/*.sql`, `models/*.ts` |

## Usage

### Command Line Interface

#### Basic Code Generation
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

#### Drift Detection
```bash
# Check for drift in generated code
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json

# Detailed drift report
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --verbose

# JSON output for CI/CD
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --format json
```

#### Watch Mode
```bash
# Watch for changes and auto-regenerate
pnpm ae-framework codegen watch -i .ae/ae-ir.json -o generated/types -t typescript
```

### NPM Scripts

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

### Helper Scripts

The `scripts/codegen-tools.sh` script provides convenient batch operations:

```bash
# Generate all targets at once
./scripts/codegen-tools.sh generate-all

# Check drift across all generated code
./scripts/codegen-tools.sh check-drift

# Watch for changes and auto-regenerate
./scripts/codegen-tools.sh watch
```

## Configuration

### Generation Options

```typescript
interface CodegenOptions {
  inputPath: string;                    // AE-IR JSON file
  outputDir: string;                   // Output directory
  target: 'typescript' | 'react' | 'api' | 'database';
  templateDir?: string;                // Custom templates
  enableDriftDetection?: boolean;      // Enable drift detection (default: true)
  preserveManualChanges?: boolean;     // Preserve manual edits (default: true)
  hashAlgorithm?: 'sha256' | 'md5';   // Hash algorithm (default: sha256)
}
```

### Drift Detection Config

```typescript
interface DriftConfig {
  codeDir: string;                     // Generated code directory
  specPath: string;                    // AE-IR specification file
  ignorePatterns?: string[];           // Files to ignore
  verbose?: boolean;                   // Detailed reporting
  autoFix?: boolean;                   // Auto-fix minor issues
}
```

## CI/CD Integration

### GitHub Actions Workflow

The system includes a comprehensive GitHub Actions workflow (`.github/workflows/codegen-drift-check.yml`) that:

1. **Detects Drift**: Analyzes changes in specifications and generated code
2. **Regenerates Code**: Automatically regenerates outdated code
3. **Validates Output**: Ensures generated code compiles and passes checks
4. **Comments on PRs**: Provides detailed drift reports in pull requests
5. **Quality Gates**: Prevents merging with critical drift issues

### Workflow Triggers

- Push to main branch with spec changes
- Pull requests modifying specifications
- Changes to codegen system or templates

### Exit Codes

| Code | Status | Meaning |
|------|--------|---------|
| 0 | `no_drift` | No drift detected |
| 1 | `minor_drift` | Minor changes, regeneration recommended |
| 2 | `major_drift` | Major changes, regeneration required |
| 3 | `critical_drift` | Critical changes, immediate action required |

## Drift Detection Levels

### No Drift ✅
- Generated code matches specification exactly
- No manual modifications detected
- All files present and unchanged

### Minor Drift ⚠️  
- Small manual modifications to generated files
- Non-critical changes that don't affect functionality
- Can be auto-fixed in most cases

### Major Drift 🟠
- Significant changes to generated files
- Multiple files modified manually
- Regeneration recommended but not critical

### Critical Drift 🚨
- Specification has changed significantly
- Many files deleted or heavily modified
- Immediate regeneration required

## Development Workflow

### 1. Specification Changes
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

### 2. Local Development
```bash
# Start watch mode for real-time updates
pnpm codegen:watch

# In another terminal, edit specifications
# Watch mode will automatically regenerate code
```

### 3. Pre-commit Validation
```bash
# Before committing, check for drift
pnpm codegen:drift

# Validate generated code compiles
pnpm codegen:validate

# Check generation status
pnpm codegen:status
```

## Generated File Structure

### TypeScript Target
```
generated/typescript/
├── .codegen-manifest.json     # Generation metadata
├── types/
│   └── domain.ts              # Domain entity types
├── schemas/
│   └── validation.ts          # Zod validation schemas
└── api.ts                     # API interface definitions
```

### React Target
```
generated/react/
├── .codegen-manifest.json
├── components/
│   ├── UserForm.tsx           # Entity form components
│   ├── UserList.tsx           # Entity list components
│   ├── ProductForm.tsx
│   └── ProductList.tsx
```

### API Target
```
generated/api/
├── .codegen-manifest.json
└── handlers/
    ├── users_get.ts           # GET /users handler
    ├── users_post.ts          # POST /users handler
    └── products_get.ts        # GET /products handler
```

### Database Target
```
generated/database/
├── .codegen-manifest.json
├── migrations/
│   └── 001_initial_schema.sql # SQL migration scripts
└── models/
    ├── User.ts                # TypeORM entity models
    └── Product.ts
```

## Manifest File Format

Each generated directory contains a `.codegen-manifest.json` file:

```json
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

## Best Practices

### 1. Specification Management
- Keep AE-IR files in version control
- Use descriptive commit messages when updating specs
- Tag specification versions for release management

### 2. Generated Code Handling
- **DO NOT** manually edit generated files
- Add `// DO NOT MODIFY` headers to generated files
- Use `.gitignore` for generated directories if not committing

### 3. Drift Management
- Run drift detection regularly during development
- Address drift issues promptly to avoid accumulation
- Use CI/CD quality gates to prevent drift in production

### 4. Template Customization
- Create organization-specific templates
- Version control template files
- Test template changes with existing specifications

## Troubleshooting

### Common Issues

#### "No AE-IR file found"
```bash
# Solution: Compile specification first
pnpm ae-framework spec compile -i spec/my-spec.md -o .ae/ae-ir.json
```

#### "Drift detection failed"
```bash
# Solution: Check manifest file exists
ls generated/*/.codegen-manifest.json

# Regenerate if manifest missing
pnpm codegen:generate
```

#### "Generated code doesn't compile"
```bash
# Solution: Validate and regenerate
pnpm codegen:validate
pnpm codegen:regen
```

### Debug Mode

Enable verbose output for detailed debugging:

```bash
# Verbose drift detection
pnpm ae-framework codegen drift -d generated/types -s .ae/ae-ir.json --verbose

# Verbose generation
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/types -t typescript --verbose
```

### Manual Recovery

If the system gets into an inconsistent state:

```bash
# Clean all generated code
pnpm codegen:clean

# Regenerate everything from scratch
pnpm codegen:generate

# Verify status
pnpm codegen:status
```

## Integration with Other Systems

### Spec Compiler Integration
The codegen system works seamlessly with the AE-Spec compiler:

```bash
# Compile spec and generate code in one workflow
pnpm ae-framework spec compile -i spec/my-spec.md -o .ae/ae-ir.json
pnpm ae-framework codegen generate -i .ae/ae-ir.json -o generated/types -t typescript
```

### Build System Integration
Add to your build pipeline:

```json
{
  "scripts": {
    "prebuild": "pnpm codegen:drift && pnpm codegen:validate",
    "build": "tsc",
    "postbuild": "pnpm codegen:status"
  }
}
```

## Metrics and Monitoring

The system tracks:
- Generation success/failure rates
- Drift detection frequency and severity
- Code validation results
- Performance metrics (generation time, file counts)

Access metrics through:
- GitHub Actions artifacts
- CI/CD dashboard integration
- Local status reports

This comprehensive system ensures that your generated code stays consistent, up-to-date, and reliable throughout the development lifecycle.