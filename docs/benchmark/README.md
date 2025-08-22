# AE Framework Benchmark Integration

## Overview

The AE Framework Benchmark Integration provides performance evaluation against the [Req2Run-Benchmark](https://github.com/itdojp/req2run-benchmark) dataset.

## Quick Start

```bash
# List available problems
ae-benchmark list

# Run basic problems
ae-benchmark run --difficulty basic

# Run CI-optimized benchmarks
ae-benchmark run --ci

# Generate configuration
ae-benchmark init
```

## NPM Scripts

```bash
# Quick execution
npm run benchmark:basic

# CI execution
npm run benchmark:ci

# List problems
npm run benchmark:list
```

## Features

- 🏆 Multiple difficulty levels (Basic → Expert)
- 📊 Comprehensive metrics collection
- 🚀 Parallel execution support
- 📈 Rich reporting formats
- 🔧 Flexible configuration

## Related

- [Issue #155: Benchmark Integration](https://github.com/itdojp/ae-framework/issues/155)
- [Req2Run-Benchmark Repository](https://github.com/itdojp/req2run-benchmark)