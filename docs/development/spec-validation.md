# AE-Spec Validation System

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
npm run validate:specs

# Validate specific file
npm run validate:spec spec/my-spec.md

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
npm run hooks:setup-spec-validation
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

## Usage Scenarios

### 1. Developer Workflow

```bash
# 1. Create/modify specification
vim spec/my-new-feature.md

# 2. Validate locally
npm run validate:spec spec/my-new-feature.md

# 3. Fix any issues and re-validate
npm run validate:spec spec/my-new-feature.md

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
   npm run build
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
  validate-specs = !npm run validate:specs
  validate-spec = "!f() { npm run validate:spec \"$1\"; }; f"
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

Results are stored in `validation-results/` directory and uploaded as CI artifacts for analysis.