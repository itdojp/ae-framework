# Parallel Execution Strategy

> 🌍 Language / 言語: English | 日本語

## Overview

The AE Framework implements a sophisticated parallel test execution strategy that maximizes CI efficiency while maintaining test reliability and resource optimization.

## Key Components

### 1. Podman-based Standardization
- **Containerized Test Environment**: All tests run in standardized Podman containers (Docker Desktop fallback is supported)
- **Resource Constraints**: Consistent CPU and memory limits across test types
- **Isolation**: Each test suite runs in its own container to prevent interference

### 2. Intelligent Test Distribution

#### Test Suite Matrix
| Suite | Priority | Resource Weight | Est. Duration | Dependencies |
|-------|----------|----------------|---------------|--------------|
| Unit | 1 | 1 | 5 min | None |
| Integration | 2 | 2 | 10 min | Unit |
| Quality | 2 | 2 | 15 min | None |
| E2E | 3 | 3 | 20 min | Unit, Integration |
| Flake Detection | 4 | 2 | 13 min | None |

#### Resource Allocation
- **CPU Limits**: 0.5-2.0 cores per container
- **Memory Limits**: 512MB-3GB based on test type
- **Concurrency**: Maximum 4 parallel containers
- **Load Balancing**: Dynamic resource weight consideration

### 3. Execution Strategies

#### GitHub Actions Matrix Strategy
```yaml
strategy:
  fail-fast: false
  matrix:
    test-type: [unit, integration, quality, flake-detection]
```

#### Local Parallel Coordination
```bash
# Run all test suites in parallel with optimal resource allocation
pnpm run test:parallel

# Podman-based parallel execution with resource constraints (Docker Desktop fallback supported)
make test:docker:all
```

## Usage

### CI/CD Integration

The parallel execution strategy automatically activates in GitHub Actions:

1. **Matrix Jobs**: Unit, Integration, Quality, and Flake Detection run in parallel
2. **Separate E2E**: E2E tests run separately due to higher resource requirements
3. **Performance Tests**: Run only on main branch pushes
4. **Result Consolidation**: All results are merged into a comprehensive report

### Local Development

#### Quick Parallel Run
```bash
pnpm run test:parallel
```

#### Podman-based Execution (Docker Desktop fallback)
```bash
# All test suites
make test:docker:all

# Specific test suite
make test:docker:unit
make test:docker:integration
make test:docker:e2e
```
> ℹ️ `make test:docker:*` ターゲットは Podman の Docker 互換 CLI (`podman`/`podman-compose`) 上でもそのまま動作します。Docker Desktop を利用する場合も同じコマンドが使用可能です。

#### Manual Coordination
```bash
# Start parallel coordinator with custom settings
node scripts/parallel-test-coordinator.mjs
```

## Performance Optimization

### Resource Management
- **Dynamic Load Balancing**: Jobs start based on available resources
- **Dependency Management**: Tests with dependencies wait for prerequisites
- **Adaptive Timeouts**: Each test type has optimized timeout settings

### Efficiency Metrics
- **Parallel Efficiency**: Measures how well parallel execution performs vs sequential
- **Resource Utilization**: Tracks CPU and memory usage across containers
- **Duration Variance**: Monitors actual vs estimated execution times

### Example Output
```
🚀 Starting parallel test execution coordinator...
📊 Available CPU cores: 8, Max concurrency: 4
🏃 Starting unit test suite (priority: 1, weight: 1)
🏃 Starting quality test suite (priority: 2, weight: 2)
✅ unit completed successfully in 4.2s
🏃 Starting integration test suite (priority: 2, weight: 2)
✅ quality completed successfully in 12.8s
🏃 Starting e2e test suite (priority: 3, weight: 3)
✅ integration completed successfully in 8.9s
🏃 Starting flake-detection test suite (priority: 4, weight: 2)
✅ e2e completed successfully in 18.5s
✅ flake-detection completed successfully in 11.2s
📊 Execution report saved: reports/parallel-execution/execution-report-1234567890.json
⏱️  Total execution time: 21.4s
🎯 Parallel efficiency: 87.3%
```

## Monitoring and Reports

### Execution Reports
- **Performance Metrics**: Duration, efficiency, resource utilization
- **Job Analysis**: Individual test suite performance and variance
- **Optimization Recommendations**: Automated suggestions for improvement

### Log Management
- **Individual Logs**: Each test suite maintains separate execution logs
- **Consolidated Output**: Combined results in standardized format
- **Error Analysis**: Failed job details with recommendations

## Adaptive Features

### Flaky Test Handling
- **Automatic Retry**: Failed tests trigger enhanced flake detection
- **Pattern Analysis**: Identifies root causes of test instability
- **Isolation Management**: Problematic tests can be isolated automatically

### Resource Adaptation
- **Dynamic Scaling**: Adjusts concurrency based on available resources
- **Load Distribution**: Balances test execution based on resource weights
- **Timeout Management**: Adaptive timeouts based on historical performance

## Configuration

### Environment Variables
```bash
# Maximum concurrent test containers
MAX_TEST_CONCURRENCY=4

# Resource weight multiplier
RESOURCE_WEIGHT_MULTIPLIER=1.0

# Enable adaptive timeouts
ADAPTIVE_TIMEOUTS=true
```

### Podman Compose Override
```yaml
# podman-compose.override.yaml (Docker Desktop users can reuse the same file)
services:
  test-unit:
    deploy:
      resources:
        limits:
          cpus: '1.5'  # Custom CPU limit
          memory: 1.5G # Custom memory limit
```

## Best Practices

### Test Design
1. **Independence**: Ensure tests can run in any order
2. **Cleanup**: Proper resource cleanup in each test
3. **Timeouts**: Realistic timeout expectations
4. **Dependencies**: Minimize inter-test dependencies

### Resource Optimization
1. **Right-sizing**: Allocate appropriate resources per test type
2. **Cleanup**: Clean Docker volumes and images regularly
3. **Monitoring**: Track resource usage and optimize accordingly
4. **Scaling**: Adjust concurrency based on available hardware

### CI Optimization
1. **Caching**: Leverage Docker layer caching
2. **Artifacts**: Preserve test results and reports
3. **Matrix Strategy**: Use GitHub Actions matrix for optimal parallelization
4. **Fail-fast**: Balance between early failure detection and comprehensive testing

## Troubleshooting

### Common Issues

#### Resource Exhaustion
- **Symptom**: Tests timeout or fail with memory errors
- **Solution**: Reduce concurrency or increase resource limits

#### Podman/Docker Issues
- **Symptom**: Container start failures or permission errors
- **Solution**: Check Podman service status (`podman info`) or Docker daemon permissions

#### Dependency Conflicts
- **Symptom**: Tests fail when run in parallel but pass individually
- **Solution**: Review test isolation and shared resource usage

### Debugging Commands
```bash
# Check Podman resources (or `docker` if you use Docker Desktop)
podman system df

# Monitor container resources
podman stats

# View parallel execution logs
tail -f logs/parallel-*.log

# Test environment validation
make test:env:validate
```
> ℹ️ Docker Desktop を使用している場合は `podman` コマンドを `docker` へ読み替えてください。
