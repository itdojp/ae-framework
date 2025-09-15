# CI/Test Optimization Guide

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

統合 CI/テスト最適化ツールの使い方をまとめたガイドです。安定性向上、フレーク検出、性能最適化、包括的レポートを組み合わせて CI を高速かつ堅牢にします。クイックスタート/ターゲット最適化/設定例を以下に掲載しています。

This document provides comprehensive guidance for optimizing CI/CD pipelines and test execution using the Integrated CI/Test Optimizer.

## Overview

The Integrated CI/Test Optimizer combines multiple optimization strategies to improve test reliability, performance, and CI stability:

- **Stability Enhancement**: Optimizes timeouts, resource limits, and environment configuration
- **Flaky Test Detection**: Identifies and analyzes potentially unreliable tests
- **Performance Optimization**: Improves test execution speed and resource usage
- **Comprehensive Reporting**: Provides detailed analytics and recommendations

## Quick Start

### Basic Optimization
```bash
# Run complete optimization suite
pnpm run optimize:ci

# Force CI mode (useful for local testing of CI configurations)
pnpm run optimize:ci:full
```

### Targeted Optimization
```bash
# Focus on stability improvements only
pnpm run optimize:ci:stability

# Focus on flaky test detection only
pnpm run optimize:ci:flake

# Focus on performance optimization only
pnpm run optimize:ci:performance
```

## Configuration

### Default Configuration
The optimizer uses intelligent defaults based on your environment:

**CI Environment:**
- Reduced concurrency (2 threads)
- Extended timeouts (2 minutes)
- Strict cleanup enabled
- Comprehensive reporting

**Local Environment:**
- Higher concurrency (4 threads)
- Standard timeouts (1 minute)
- Flexible configuration
- Development-focused reporting

### Custom Configuration
Create `config/ci-test-optimization.json` to customize behavior:

```json
{
  "stability": {
    "timeouts": {
      "testTimeout": 180000,
      "hookTimeout": 90000,
      "teardownTimeout": 45000
    },
    "resourceLimits": {
      "maxConcurrency": 3,
      "memoryLimit": "1.5GB"
    }
  },
  "flakeDetection": {
    "threshold": 0.03,
    "minimumRuns": 10
  },
  "performance": {
    "slowTestThreshold": 15000,
    "parallelization": {
      "maxWorkers": 3
    }
  }
}
```

## Generated Optimizations

### Vitest Configuration
The optimizer generates `vitest.optimized.config.ts` with:
- Environment-specific timeouts and resource limits
- Enhanced mock and module cleanup
- Optimized parallel execution settings
- CI-specific reporters and output formats
- Coverage configuration for stability

### Package Scripts
Automatically adds optimized test execution scripts:
- `test:parallel` - Optimized parallel test execution
- `test:parallel:ci` - CI-specific parallel execution with proper reporting
- `test:performance` - Performance-focused execution (no coverage)
- `test:flake-detection` - Multi-retry execution for flake detection

## Flaky Test Detection

### Detection Strategies
1. **Historical Analysis**: Reviews past test results for failure patterns
2. **Pattern Recognition**: Identifies common flaky test indicators:
   - Timeout-related failures
   - Resource contention issues
   - Concurrency problems
   - Environment-specific failures

### Failure Pattern Categories
- **Timeout Issues**: Tests failing due to time constraints
- **Resource Issues**: Memory leaks, handle exhaustion
- **Concurrency Issues**: Race conditions, parallel execution problems
- **Environment Issues**: CI-specific, platform-dependent failures

### Recommendations
The system provides targeted recommendations based on detected patterns:
- Timeout adjustments for performance issues
- Synchronization improvements for concurrency problems
- Resource cleanup for memory-related failures

## Performance Optimization

### Memory Monitoring
- Tracks heap usage throughout test execution
- Detects potential memory leaks (> 100MB threshold)
- Provides cleanup recommendations

### Parallel Execution
- Optimizes worker thread configuration
- Balances performance vs. stability
- Adjusts chunk sizes for optimal throughput

### Smart Caching
- Enables test result caching where beneficial
- Optimizes coverage collection for CI environments
- Reduces redundant work across test runs

## Integration with CI/CD

### GitHub Actions Example
```yaml
name: Optimized Tests
on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: '20'
      
      - name: Install dependencies
        run: pnpm install --frozen-lockfile
      
      - name: Optimize CI environment
        run: pnpm run optimize:ci:full
      
      - name: Run optimized tests
        run: pnpm run test:parallel:ci
      
      - name: Upload test results
        uses: actions/upload-artifact@v4
        if: always()
        with:
          name: test-results
          path: |
            reports/
            temp-reports/
```

### Jenkins Pipeline Example
```groovy
pipeline {
    agent any
    environment {
        CI = 'true'
    }
    stages {
        stage('Setup') {
            steps {
                sh 'pnpm install --frozen-lockfile'
                sh 'pnpm run optimize:ci:full'
            }
        }
        stage('Test') {
            steps {
                sh 'pnpm run test:parallel:ci'
            }
            post {
                always {
                    publishTestResults testResultsPattern: 'reports/junit-results.xml'
                    archiveArtifacts artifacts: 'reports/**, temp-reports/**'
                }
            }
        }
    }
}
```

## Monitoring and Analytics

### Generated Reports
The optimizer creates comprehensive reports in `reports/ci-optimization/`:

1. **optimization-report.json**: Detailed JSON report with metrics
2. **optimization-summary.md**: Human-readable summary
3. **test-results.json**: Detailed test execution data (if available)

### Key Metrics
- **Execution Time**: Total optimization and test execution time
- **Memory Usage**: Peak and average memory consumption
- **Flaky Test Count**: Number of potentially unreliable tests
- **Applied Optimizations**: List of all improvements made
- **Performance Issues**: Detected bottlenecks and recommendations

### Continuous Monitoring
Set up regular monitoring to track optimization effectiveness:

```bash
# Weekly optimization analysis
0 0 * * 1 cd /path/to/project && pnpm run optimize:ci > optimization-$(date +%Y%m%d).log

# Daily flaky test detection
0 8 * * * cd /path/to/project && pnpm run optimize:ci:flake
```

## Best Practices

### Development Workflow
1. **Local Development**: Use standard test commands for rapid feedback
2. **Pre-commit**: Run `pnpm run optimize:ci:flake` to catch potential issues
3. **CI/CD**: Use optimized configurations for reliable automation
4. **Regular Reviews**: Analyze optimization reports weekly

### Test Writing Guidelines
1. **Avoid Hard-coded Timeouts**: Use configurable timeouts from environment
2. **Proper Cleanup**: Always clean up resources in test teardown
3. **Isolated Tests**: Ensure tests don't depend on shared state
4. **Deterministic Behavior**: Avoid random values or timing dependencies

### CI Configuration
1. **Resource Allocation**: Match CI resources to optimization settings
2. **Timeout Configuration**: Set job timeouts based on optimization metrics
3. **Retry Policies**: Use smart retry for known flaky tests
4. **Artifact Collection**: Always preserve optimization reports

## Troubleshooting

### Common Issues

**Tests Timing Out in CI**
```bash
# Increase timeouts for CI environment
pnpm run optimize:ci:stability
# Check generated vitest.optimized.config.ts for timeout values
```

**High Memory Usage**
```bash
# Enable memory monitoring
pnpm run optimize:ci:performance
# Review reports/ci-optimization/optimization-report.json for memory metrics
```

**Flaky Test Detection False Positives**
```bash
# Adjust detection threshold in config/ci-test-optimization.json
{
  "flakeDetection": {
    "threshold": 0.08,  // Increase from default 0.05
    "minimumRuns": 8    // Require more runs for detection
  }
}
```

### Debug Mode
Enable verbose logging for troubleshooting:
```bash
DEBUG=ci-optimizer pnpm run optimize:ci
```

## Advanced Usage

### Custom Optimization Strategies
Extend the optimizer with custom strategies:

```javascript
import { IntegratedCITestOptimizer } from './scripts/integrated-ci-test-optimizer.mjs';

class CustomOptimizer extends IntegratedCITestOptimizer {
  async customOptimization() {
    // Implement custom optimization logic
    console.log('Applying custom optimizations...');
    
    // Example: Custom test filtering
    const customConfig = {
      ...this.config,
      customFilter: {
        excludePatterns: ['**/*.slow.test.*'],
        includeOnly: process.env.TEST_SUITE || '**'
      }
    };
    
    return customConfig;
  }
}

const optimizer = new CustomOptimizer();
await optimizer.run();
```

### Integration with Other Tools
The optimizer integrates well with:
- **Jest**: Adapt configuration for Jest-based projects
- **Cypress**: Optimize E2E test execution
- **Playwright**: Enhance browser test reliability
- **Docker**: Containerized test environment optimization

## Migration Guide

### From Existing CI Scripts
1. **Backup Current Configuration**: Save existing CI configurations
2. **Run Initial Optimization**: `pnpm run optimize:ci` to generate baseline
3. **Compare Results**: Review generated configurations vs. current setup
4. **Gradual Migration**: Start with non-critical pipelines
5. **Monitor Performance**: Track improvements and adjust as needed

### Version Compatibility
- **Node.js**: Requires Node.js 18+ for optimal performance
- **Vitest**: Compatible with Vitest 1.0+
- **Jest**: Requires manual configuration adaptation
- **CI Platforms**: Tested with GitHub Actions, Jenkins, GitLab CI

## Support and Resources

### Documentation
- [Vitest Configuration Guide](https://vitest.dev/config/)
- [CI Best Practices](./testing/ci-best-practices.md)
- [Performance Optimization](./testing/performance-optimization.md)

### Community
- Report issues via GitHub Issues
- Contribute improvements via Pull Requests
- Share optimization strategies in Discussions

---

*Generated by Integrated CI/Test Optimizer - Enhancing test reliability and performance*
