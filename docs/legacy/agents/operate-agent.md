# Operate Agent - Phase 6 of ae-framework

> **🌍 Language / 言語**: [English](#english) | [日本語](#japanese)

---

## English

The Operate Agent is the final phase in the ae-framework's 6-phase cycle (Intent→Formal→Tests→Code→Verify→**Operate**). It handles production operations, monitoring, and optimization to ensure deployed systems run reliably, efficiently, and securely.

## Overview

The Operate Agent provides comprehensive production operations capabilities including:

- **Deployment Orchestration**: CI/CD integration with blue-green, canary, and rolling deployment strategies
- **Infrastructure Monitoring**: Real-time health checks and alerting across all system endpoints  
- **Performance Optimization**: Automated performance analysis and tuning recommendations
- **Log Analysis**: Intelligent log aggregation, pattern detection, and anomaly identification
- **Incident Management**: Complete incident lifecycle management from creation to resolution
- **Resource Scaling**: Dynamic auto-scaling based on performance metrics and demand
- **Security Monitoring**: Vulnerability scanning and compliance framework validation
- **Cost Optimization**: Infrastructure cost analysis and optimization recommendations
- **Chaos Engineering**: Controlled resilience testing through chaos experiments
- **SLO/SLA Tracking**: Service level objective monitoring and compliance reporting

## Architecture

### Core Components

```
src/agents/operate-agent.ts        # Core agent implementation
src/mcp-server/operate-server.ts   # MCP server wrapper
```

### Key Classes

- **OperateAgent**: Main agent class providing all operational capabilities
- **OperateServer**: MCP server providing tool interfaces for agent operations

## Configuration

The Operate Agent is configured through the `OperateAgentConfig` interface:

```typescript
interface OperateAgentConfig {
  deploymentConfig: DeploymentConfig;
  monitoringConfig: MonitoringConfig;
  alertingConfig: AlertingConfig;
  scalingConfig: ScalingConfig;
  securityConfig: SecurityConfig;
  costConfig: CostConfig;
  sloConfig: SloConfig;
  chaosConfig: ChaosConfig;
}
```

### Example Configuration

```typescript
const config: OperateAgentConfig = {
  deploymentConfig: {
    cicdProvider: 'github-actions',
    environments: ['staging', 'production'],
    rolloutStrategy: 'blue-green',
    healthCheckUrl: 'http://localhost:3000/health',
    timeoutSeconds: 300,
  },
  monitoringConfig: {
    metricsEndpoint: 'http://localhost:9090',
    logsEndpoint: 'http://localhost:3100',
    tracesEndpoint: 'http://localhost:16686',
    healthEndpoints: ['http://localhost:3000/health'],
    checkIntervalMs: 30000,
  },
  // ... other configurations
};
```

## MCP Tools

The Operate Agent exposes 10 MCP tools for external integration:

### 1. deploy_application

Orchestrate application deployments with various strategies.

**Parameters:**
- `environment` (required): Target deployment environment
- `version` (required): Application version to deploy
- `strategy` (optional): Deployment strategy (blue-green, canary, rolling)
- `rollbackOnFailure` (optional): Auto-rollback on failure
- `healthCheckTimeout` (optional): Health check timeout in seconds

**Example:**
```json
{
  "environment": "production",
  "version": "v1.2.3",
  "strategy": "blue-green",
  "rollbackOnFailure": true,
  "healthCheckTimeout": 300
}
```

### 2. monitor_health

Check system health across all monitored endpoints.

**Parameters:** None

**Returns:** Health status for all endpoints with overall system status.

### 3. analyze_logs

Analyze aggregated logs for patterns, anomalies, and insights.

**Parameters:**
- `startTime` (required): Start time (ISO 8601)
- `endTime` (required): End time (ISO 8601)
- `logLevel` (optional): Minimum log level to analyze
- `service` (optional): Specific service to analyze
- `query` (optional): Search query to filter logs

### 4. manage_incident

Handle complete incident lifecycle management.

**Parameters:**
- `action` (required): create, update, resolve, escalate
- `incidentId` (conditional): Required for update/resolve/escalate
- `title` (conditional): Required for create
- `description` (conditional): Required for create
- `severity` (optional): low, medium, high, critical
- `assignee` (optional): Person assigned to incident
- `updateNotes` (optional): Update notes for update action
- `resolution` (optional): Resolution details for resolve action

### 5. optimize_performance

Analyze performance metrics and apply optimization recommendations.

**Parameters:**
- `timeWindow` (required): Analysis time window (e.g., "1h", "24h", "7d")
- `metrics` (required): Array of metrics to analyze
- `service` (optional): Specific service to optimize
- `autoApply` (optional): Auto-apply low-risk optimizations

### 6. scale_resources

Manage resource scaling based on demand and performance.

**Parameters:**
- `service` (required): Service to scale
- `action` (optional): auto, scale-up, scale-down
- `targetInstances` (optional): Target instance count for manual scaling
- `force` (optional): Force scaling beyond safety limits

### 7. run_chaos_test

Execute chaos engineering experiments for resilience testing.

**Parameters:**
- `experiment` (required): Name of chaos experiment to run
- `dryRun` (optional): Run without causing actual disruption
- `duration` (optional): Experiment duration
- `intensity` (optional): Experiment intensity (0-100)

### 8. track_slo

Monitor SLO/SLA compliance and generate status reports.

**Parameters:** None

**Returns:** Current SLO compliance status for availability, latency, error rate, and throughput.

### 9. analyze_costs

Analyze infrastructure costs and generate optimization recommendations.

**Parameters:**
- `timeWindow` (required): Analysis time window
- `services` (optional): Specific services to analyze
- `includePredictions` (optional): Include cost forecasts

### 10. security_scan

Run security scans and compliance checks.

**Parameters:**
- `scope` (optional): infrastructure, application, dependencies, all
- `includeCompliance` (optional): Include compliance checks
- `frameworks` (optional): Specific compliance frameworks

## Usage

### Starting the MCP Server

```bash
# Production mode
npm run operate:server

# Development mode with hot reload
npm run operate:dev
```

### Direct Agent Usage

```typescript
import { OperateAgent } from './src/agents/operate-agent.js';

const agent = new OperateAgent(config);

// Deploy application
const deployResult = await agent.deployApplication({
  environment: 'production',
  version: 'v1.2.3',
  strategy: 'blue-green',
});

// Check system health
const health = await agent.monitorHealth();

// Manage scaling
const scaleResult = await agent.scaleResources({
  service: 'api-service',
  action: 'auto',
});
```

## Key Features

### Deployment Orchestration

- **Multiple Strategies**: Blue-green, canary, and rolling deployments
- **Health Verification**: Post-deployment health checks and validation
- **Automatic Rollback**: Configurable rollback on deployment failure
- **CI/CD Integration**: Support for GitHub Actions, GitLab CI, Jenkins, Tekton

### Monitoring & Alerting

- **Multi-endpoint Health Checks**: Comprehensive system health monitoring
- **Alert Channels**: Slack, email, PagerDuty, webhook integration
- **Escalation Policies**: Configurable alert escalation workflows
- **Threshold Management**: Customizable alerting thresholds

### Performance Optimization

- **Metrics Analysis**: CPU, memory, latency, throughput analysis
- **Recommendation Engine**: Automated optimization suggestions
- **Auto-application**: Low-risk optimizations can be applied automatically
- **Impact Assessment**: Estimated performance improvements

### Incident Management

- **Complete Lifecycle**: Create, update, resolve, escalate incidents
- **Severity Tracking**: Low, medium, high, critical severity levels
- **Assignment Management**: Track incident ownership and progress
- **Resolution Documentation**: Detailed incident resolution tracking

### Resource Scaling

- **Auto-scaling**: Demand-based automatic scaling decisions
- **Safety Limits**: Configurable min/max instance constraints
- **Cooldown Periods**: Prevent scaling oscillation
- **Manual Override**: Force scaling when needed

### Chaos Engineering

- **Experiment Library**: Pod failure, network latency, resource stress tests
- **Safety Boundaries**: Maximum error rates and latency limits
- **Scheduled Execution**: Automated chaos testing schedules
- **Impact Analysis**: Detailed experiment results and observations

### Security & Compliance

- **Vulnerability Scanning**: Infrastructure and application security scanning
- **Compliance Frameworks**: SOC2, PCI-DSS, and custom framework support
- **Risk Scoring**: Comprehensive security risk assessment
- **Remediation Guidance**: Actionable security recommendations

### Cost Optimization

- **Cost Analysis**: Detailed infrastructure cost breakdown
- **Budget Tracking**: Monitor spending against budget limits
- **Optimization Recommendations**: Cost reduction suggestions
- **Savings Projection**: Estimated savings from optimizations

## Integration Points

### Observability Stack

- **Metrics**: Prometheus/OpenTelemetry integration
- **Logs**: Integration with log aggregation systems
- **Traces**: Distributed tracing support
- **Dashboards**: Grafana/custom dashboard integration

### CI/CD Platforms

- GitHub Actions
- GitLab CI/CD
- Jenkins
- Tekton Pipelines

### Cloud Providers

- Kubernetes native scaling
- Cloud provider auto-scaling groups
- Container orchestration platforms
- Serverless function scaling

## Best Practices

### Deployment Safety

1. **Always Use Health Checks**: Configure comprehensive health endpoints
2. **Gradual Rollouts**: Use canary or blue-green for critical deployments
3. **Rollback Readiness**: Ensure rollback procedures are tested and automated
4. **Monitoring During Deployment**: Watch metrics closely during rollouts

### Incident Response

1. **Clear Severity Guidelines**: Define what constitutes each severity level
2. **Response Time SLAs**: Set clear response time expectations
3. **Communication Protocols**: Keep stakeholders informed during incidents
4. **Post-Incident Reviews**: Learn from every incident with retrospectives

### Performance Optimization

1. **Baseline Establishment**: Know your normal performance characteristics
2. **Gradual Changes**: Apply optimizations incrementally
3. **Impact Measurement**: Always measure the impact of changes
4. **Rollback Plans**: Be prepared to revert performance changes

### Chaos Engineering

1. **Start Small**: Begin with low-impact experiments
2. **Business Hours**: Run experiments during monitored hours
3. **Blast Radius**: Limit experiment scope to prevent widespread impact
4. **Documentation**: Record all experiments and their outcomes

## Error Handling

The Operate Agent includes comprehensive error handling:

- **Validation Errors**: Input parameter validation with clear error messages
- **Operational Errors**: Graceful handling of infrastructure failures
- **Timeout Handling**: Configurable timeouts for all operations
- **Retry Logic**: Automatic retry for transient failures
- **Circuit Breakers**: Prevent cascade failures in dependent systems

## Security Considerations

- **Credential Management**: Secure storage and rotation of access credentials
- **Least Privilege**: Minimal required permissions for operations
- **Audit Logging**: Complete audit trail of all operational actions
- **Encryption**: Secure communication with all external systems
- **Access Control**: Role-based access to operational capabilities

## Performance Characteristics

- **Scalability**: Designed for high-scale production environments
- **Efficiency**: Minimal resource overhead for monitoring operations
- **Reliability**: Built-in redundancy and failure handling
- **Responsiveness**: Fast response times for critical operations

## Future Enhancements

- **Machine Learning**: AI-driven anomaly detection and optimization
- **Predictive Scaling**: Forecast-based resource scaling
- **Advanced Chaos**: More sophisticated chaos engineering scenarios
- **Multi-Cloud**: Enhanced support for multi-cloud deployments
- **GitOps Integration**: Deep integration with GitOps workflows

## Contributing

When contributing to the Operate Agent:

1. **Test Coverage**: Ensure comprehensive test coverage for new features
2. **Documentation**: Update documentation for any new capabilities
3. **Configuration**: Add configuration options for new features
4. **Error Handling**: Include proper error handling and validation
5. **Performance**: Consider performance impact of new features

## License

This project follows the same license as the ae-framework project.

---

## Japanese

**オペレート・エージェント - ae-frameworkのフェーズ6**

オペレート・エージェントは、ae-frameworkの6フェーズサイクル（Intent→Formal→Tests→Code→Verify→**Operate**）の最終フェーズです。デプロイされたシステムが信頼性、効率性、セキュリティを保って動作することを確保するために、本番運用、監視、最適化を処理します。

## 概要

オペレート・エージェントは以下を含む包括的な本番運用機能を提供します：

- **デプロイオーケストレーション**: ブルーグリーン、カナリア、ローリングデプロイ戦略によるCI/CD統合
- **インフラ監視**: 全システムエンドポイントでのリアルタイムヘルスチェックとアラート
- **パフォーマンス最適化**: 自動パフォーマンス分析と調整推奨
- **ログ分析**: インテリジェントなログ集約、パターン検出、異常識別
- **インシデント管理**: 作成から解決まで完全なインシデントライフサイクル管理
- **リソーススケーリング**: パフォーマンス指標と需要に基づく動的オートスケーリング
- **セキュリティ監視**: 脆弱性スキャンとコンプライアンスフレームワーク検証
- **コスト最適化**: インフラコスト分析と最適化推奨
- **カオスエンジニアリング**: カオス実験による制御された回復力テスト
- **SLO/SLA追跡**: サービスレベル目標監視とコンプライアンス報告

## アーキテクチャ

### 中核コンポーネント

```
src/agents/operate-agent.ts        # コアエージェント実装
src/mcp-server/operate-server.ts   # MCPサーバーラッパー
```

### 主要クラス

```typescript
class OperateAgent {
  // デプロイ管理
  async deployApplication(config: DeploymentConfig): Promise<DeploymentResult>;
  async rollbackDeployment(deploymentId: string): Promise<RollbackResult>;
  
  // 監視とアラート
  async monitorInfrastructure(config: MonitoringConfig): Promise<MonitoringStatus>;
  async analyzePerformance(metrics: PerformanceMetrics): Promise<AnalysisResult>;
  
  // インシデント管理
  async createIncident(details: IncidentDetails): Promise<IncidentReport>;
  async resolveIncident(incidentId: string): Promise<ResolutionResult>;
  
  // スケーリングと最適化
  async scaleResources(policy: ScalingPolicy): Promise<ScalingResult>;
  async optimizeInfrastructure(targets: OptimizationTargets): Promise<OptimizationReport>;
}
```

## 主要機能

### デプロイオーケストレーション

```typescript
// ブルーグリーンデプロイ
const deploymentResult = await operateAgent.deployApplication({
  strategy: 'blue-green',
  application: 'user-service',
  version: 'v2.1.0',
  healthCheck: '/health',
  rollbackThreshold: 5, // 5%のエラー率で自動ロールバック
  monitoring: {
    metrics: ['response_time', 'error_rate', 'throughput'],
    duration: 600 // 10分間監視
  }
});

console.log('デプロイ結果:', deploymentResult);
```

### パフォーマンス監視

```typescript
// パフォーマンス分析の実行
const analysis = await operateAgent.analyzePerformance({
  timeRange: '1h',
  services: ['api-gateway', 'user-service', 'payment-service'],
  metrics: ['cpu', 'memory', 'response_time', 'throughput'],
  alertThresholds: {
    cpu: 80,
    memory: 85,
    response_time: 1000
  }
});

if (analysis.recommendations.length > 0) {
  console.log('最適化推奨:', analysis.recommendations);
}
```

### インシデント管理

```typescript
// インシデントの作成と追跡
const incident = await operateAgent.createIncident({
  title: 'API応答時間増大',
  severity: 'high',
  description: 'ユーザーサービスの応答時間が平常時の3倍に増大',
  affectedServices: ['user-service'],
  detectedAt: new Date(),
  reporter: 'monitoring-system',
  tags: ['performance', 'user-impact']
});

// インシデント解決
await operateAgent.resolveIncident(incident.id, {
  resolution: 'データベース接続プールサイズを増加',
  rootCause: 'データベース接続制限によるボトルネック',
  preventiveMeasures: ['接続プール監視アラート追加', 'オートスケーリングポリシー調整']
});
```

## 設定オプション

### デプロイ設定

```typescript
interface DeploymentConfig {
  strategy: 'blue-green' | 'canary' | 'rolling';
  application: string;
  version: string;
  environment: 'staging' | 'production';
  healthCheck: {
    endpoint: string;
    timeout: number;
    retries: number;
  };
  rollbackPolicy: {
    autoRollback: boolean;
    errorThreshold: number;
    timeout: number;
  };
}
```

### 監視設定

```typescript
interface MonitoringConfig {
  services: string[];
  metrics: string[];
  alerting: {
    channels: ('email' | 'slack' | 'pagerduty')[];
    severity: 'low' | 'medium' | 'high' | 'critical';
    suppressionRules: SuppressionRule[];
  };
  retention: {
    metrics: string;     // "30d"
    logs: string;        // "7d"
    traces: string;      // "3d"
  };
}
```

## MCPツール

### 利用可能なツール

1. **deploy_application**: アプリケーションデプロイの実行
2. **monitor_infrastructure**: インフラ監視の開始/設定
3. **analyze_performance**: パフォーマンス分析の実行
4. **manage_incidents**: インシデント管理操作
5. **scale_resources**: リソーススケーリングの実行
6. **optimize_infrastructure**: インフラ最適化の実行
7. **run_chaos_experiment**: カオスエンジニアリング実験の実行

### ツール使用例

```typescript
// MCPクライアントから使用
const result = await mcpClient.callTool('deploy_application', {
  strategy: 'canary',
  application: 'frontend-app',
  version: 'v1.2.3',
  trafficSplit: 10, // 10%のトラフィックを新バージョンに
  monitoring: {
    duration: 1800, // 30分間監視
    successCriteria: {
      errorRate: '<1%',
      responseTime: '<500ms'
    }
  }
});
```

## 統合

### CI/CDパイプライン

```yaml
# GitHub Actionsでの使用例
- name: AE Framework本番デプロイ
  run: |
    npm run operate-agent -- deploy \
      --strategy blue-green \
      --app user-service \
      --version ${{ github.sha }} \
      --health-check /health \
      --auto-rollback true
```

### 監視システム

- **Prometheus**: メトリクス収集と保存
- **Grafana**: 可視化とダッシュボード
- **Jaeger**: 分散トレーシング
- **ELK Stack**: ログ集約と分析

### アラートマネージャー

- **PagerDuty**: インシデント通知とエスカレーション
- **Slack**: チーム通知
- **Email**: 基本アラート配信

## ベストプラクティス

### デプロイの安全性

1. **常にヘルスチェックを使用**: 包括的なヘルスエンドポイントを設定
2. **段階的ロールアウト**: 重要なデプロイにはカナリアまたはブルーグリーンを使用
3. **ロールバック準備**: ロールバック手順をテストし自動化
4. **デプロイ中の監視**: ロールアウト中にメトリクスを注意深く監視

### インシデント対応

1. **明確な重要度ガイドライン**: 各重要度レベルを構成するものを定義
2. **応答時間SLA**: 明確な応答時間期待値を設定
3. **コミュニケーションプロトコル**: インシデント中にステークホルダーに情報提供
4. **インシデント後レビュー**: 振り返りですべてのインシデントから学習

### パフォーマンス最適化

1. **ベースライン確立**: 通常のパフォーマンス特性を把握
2. **段階的変更**: 最適化を段階的に適用
3. **影響測定**: 変更の影響を常に測定
4. **ロールバック計画**: パフォーマンス変更を元に戻す準備

## セキュリティ考慮事項

- **認証情報管理**: アクセス認証情報の安全な保存とローテーション
- **最小特権**: 操作に必要な最小限の権限
- **監査ログ**: すべての運用アクションの完全な監査証跡
- **暗号化**: すべての外部システムとの安全な通信
- **アクセス制御**: 運用機能へのロールベースアクセス

## パフォーマンス特性

- **スケーラビリティ**: 大規模本番環境向けに設計
- **効率性**: 監視操作の最小限のリソースオーバーヘッド
- **信頼性**: 組み込み冗長性と障害処理
- **応答性**: 重要な操作の高速応答時間

## 将来の拡張

- **機械学習**: AI駆動の異常検出と最適化
- **予測スケーリング**: 予測ベースのリソーススケーリング
- **高度なカオス**: より洗練されたカオスエンジニアリングシナリオ
- **マルチクラウド**: マルチクラウドデプロイの強化サポート
- **GitOps統合**: GitOpsワークフローとの深い統合

## ライセンス

このプロジェクトはae-frameworkプロジェクトと同じライセンスに従います。