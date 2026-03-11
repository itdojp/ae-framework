---
docRole: ssot
lastVerified: 2026-03-11
owner: phase-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Phase 6 Telemetry Configuration

> 🌍 Language / 言語: English | 日本語

---

## English (Overview)

Phase 6 (UI/UX & Frontend Delivery) instruments metrics, traces, and logs via OpenTelemetry to quantify quality gates and continuous improvement.

Key metrics
- Quality: Test Coverage (≥80%), A11y (≥95%), Performance (≥75%)
- Efficiency: Scaffold time (<30s), E2E test time (<5m), Build time
- Maintainability: Component complexity (<10), Unused CSS (<5%), Design token coverage (≥95%)

Configuration: environment variables to disable/enable telemetry and configure OTLP exporters.

> Note: Threshold values are implementation constants (`src/telemetry/phase6-metrics.ts`) and are not equal to a CI pass guarantee by themselves.

## Overview

ae-frameworkのPhase 6（UI/UX & Frontend Delivery）では、OpenTelemetryを使用してメトリクス・トレース・ログの計測を行います。これにより、品質ゲート引き上げの判断材料を定量化し、継続的改善を実現します。

## 📊 計測対象

### Quality Metrics (品質メトリクス)
- **Test Coverage**: テストカバレッジ率 (目標: ≥80%)
- **A11y Score**: アクセシビリティスコア (目標: ≥95%)
- **Performance Score**: パフォーマンススコア (目標: ≥75%)

### Efficiency Metrics (効率性メトリクス)
- **Scaffold Time**: UI生成時間 (目標: <30秒)
- **E2E Test Time**: E2Eテスト実行時間 (目標: <5分)
- **Build Time**: ビルド時間

### Maintainability Metrics (保守性メトリクス)
- **Component Complexity**: コンポーネント複雑度 (目標: <10)
- **CSS Unused Rate**: 未使用CSS率 (目標: <5%)
- **Design Token Coverage**: デザイントークン使用率 (目標: ≥95%)

## 🔧 Configuration

### Environment Variables

```text
# Telemetry control
DISABLE_TELEMETRY=true          # テレメトリを無効化
DEBUG_TELEMETRY=true            # デバッグログを有効化

# OTLP export configuration (optional)
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317
OTEL_EXPORTER_OTLP_TRACES_ENDPOINT=http://localhost:4317/v1/traces
OTEL_EXPORTER_OTLP_METRICS_ENDPOINT=http://localhost:4317/v1/metrics

# Service identification
NODE_ENV=production             # Environment (development/production)
```

### Default Behavior

- **Development**: Console exporterでローカル出力
- **Production**: OTLP endpointが設定されていればOTLP export、未設定ならConsole export
- **Disabled**: `DISABLE_TELEMETRY=true`で完全無効化

## 📈 Usage Examples

### CLI Commands with Telemetry

```text
# UI scaffold with telemetry
npx ae-framework ui-scaffold --components

# Output includes timing/threshold logs when metrics are recorded.
# Exact numeric values depend on the current project state.
```

### Programmatic Usage

```text
import { Phase6Telemetry } from '@ae-framework/phase6-metrics';

// Instrument scaffold operation
const result = await Phase6Telemetry.instrumentScaffoldOperation(
  'generate_components',
  async () => {
    // Your scaffold logic here
    return await generateComponents();
  },
  {
    entity_count: 3,
    target_entity: 'Product',
  }
);

// Record quality metrics
Phase6Telemetry.recordQualityMetrics({
  coverage: 85,
  a11yScore: 96,
  performanceScore: 78,
});

// Log efficiency summary
Phase6Telemetry.logEfficiencyMetrics({
  scaffoldTime: 25000, // 25 seconds
  e2eTestTime: 180000, // 3 minutes
  buildTime: 45000,    // 45 seconds
});
```

## 🎯 Threshold Configuration

### Performance Thresholds

```text
export const PHASE6_THRESHOLDS = {
  scaffoldTime: 30000,    // 30 seconds
  e2eTestTime: 300000,    // 5 minutes
  coverage: 80,           // 80%
  a11yScore: 95,          // 95%
  performanceScore: 75,   // 75%
} as const;
```

### Threshold Violations

閾値を超過した場合、自動的に警告が出力されます：

```text
⚠️ Scaffold operation 'generate_components' took 35243ms (threshold: 30000ms)
⚠️ Test coverage below threshold: 75% < 80%
⚠️ Accessibility score below threshold: 92% < 95%
```

## 📋 Instrumented Operations

### 1. Scaffold Operations
- **span**: `phase6.scaffold.{operation_name}`
- **metrics**: scaffold_operations_total, scaffold_duration_ms
- **attributes**: operation, entity_count, status, duration_ms

### 2. E2E Tests
- **span**: `phase6.e2e.{test_name}`
- **metrics**: e2e_tests_total, e2e_test_duration_ms
- **attributes**: test_name, status, duration_ms

### 3. Accessibility Audits
- **span**: `phase6.a11y.{audit_name}`
- **metrics**: a11y_audits_total
- **attributes**: audit_name, status, violations_count

### 4. Build Operations
- **span**: `phase6.build.{build_type}`
- **metrics**: build_duration_ms
- **attributes**: build_type, status, output_size

## 🔍 Monitoring & Observability

### Local Development

```text
# Run with debug telemetry
DEBUG_TELEMETRY=true npx ae-framework ui-scaffold --components

# Output:
# 📊 OpenTelemetry initialized for ae-framework Phase 6
#    Service: ae-framework v1.0.0
#    Environment: development
#    OTLP Export: ❌ Console only
```

### Production Setup

```text
# OTLP collector setup
export OTEL_EXPORTER_OTLP_ENDPOINT=http://jaeger:14268/api/traces
export NODE_ENV=production

# Run with OTLP export
npx ae-framework ui-scaffold --components
```

### CI Integration

`phase6-validation.yml` には a11y/visual/Lighthouse/coverage などのジョブがあります。  
一方で、`ae-framework ui-scaffold` を常に実行してテレメトリを収集する構成にはなっていません（2026-02-18 時点）。

必要に応じて、以下のような専用ステップを追加して収集してください：

```text
# .github/workflows/phase6-validation.yml
- name: Run UI Scaffold with Telemetry
  run: |
    DEBUG_TELEMETRY=true pnpm run ae-framework -- ui-scaffold --components
    # Emits telemetry init logs and threshold warnings to stdout
    # (or exports to OTLP when exporter is configured)
```

## 🚀 Future Roadmap

### Phase 6.1 (Current)
- ✅ Console exporter
- ✅ Basic metrics (timing, counts)
- ✅ Threshold monitoring

### Phase 6.2 (Planned)
- 🔄 OTLP export to observability platform
- 🔄 Grafana dashboard integration
- 🔄 Alert configurations

### Phase 6.3 (Future)
- 📋 Machine learning-based threshold optimization
- 📋 Predictive quality analytics
- 📋 Automated performance recommendations

## 📚 Related Documentation

- [Phase 6 Overview](./phase-6-uiux.md)
- [Quality Gates Configuration](../development/centralized-quality-gates.md)
- [OpenTelemetry Official Documentation](https://opentelemetry.io/docs/)

---

**Phase 6 Telemetry** - Measuring and improving UI/UX delivery efficiency 📊
