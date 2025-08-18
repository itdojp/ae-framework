# Centralized Quality Gates System

The AE-Framework implements a comprehensive centralized quality gates system that ensures consistent quality standards across all development phases and environments.

## Overview

The centralized quality gates system provides:

- **Single Source of Truth**: All quality thresholds defined in one JSON configuration file
- **Environment-Specific Overrides**: Different standards for development, CI, and production
- **Phase-Aware Enforcement**: Quality gates activate based on development phase progression
- **Automated CI/CD Integration**: GitHub Actions workflows enforce quality standards
- **Flexible Configuration**: Easy to modify thresholds and add new quality gates

## Architecture

### Core Components

```
policy/
├── quality.json              # Centralized policy configuration
src/utils/
├── quality-policy-loader.ts  # TypeScript utility for loading policy
scripts/
├── run-quality-gates.cjs     # Main quality gate runner
├── check-a11y-threshold.cjs  # Accessibility checker (updated)
├── check-coverage-threshold.cjs # Coverage checker (new)
.github/workflows/
├── quality-gates-centralized.yml # Comprehensive CI workflow
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

```json
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
npm run quality:gates

# Run with specific environment
npm run quality:gates:dev
npm run quality:gates:prod

# Run specific gates only
npm run quality:accessibility
npm run quality:coverage

# Run comprehensive quality check
npm run quality:all
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

```typescript
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

## Implementation Details

### Policy Loading and Overrides

The policy loader applies environment-specific overrides using a dot-notation path system:

```json
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
```json
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
```javascript
// In scripts/run-quality-gates.cjs
case 'myCustomGate':
  command = 'npm run custom-check';
  break;
```

3. **Add NPM Script**:
```json
{
  "scripts": {
    "quality:custom": "node scripts/run-quality-gates.cjs --gates=myCustomGate"
  }
}
```

### Modifying Thresholds

Simply update the `policy/quality.json` file:

```json
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

```json
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