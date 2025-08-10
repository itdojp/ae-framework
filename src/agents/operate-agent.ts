import { z } from 'zod';
import pino from 'pino';

// Core interfaces for the Operate Agent
export interface OperateAgentConfig {
  deploymentConfig: DeploymentConfig;
  monitoringConfig: MonitoringConfig;
  alertingConfig: AlertingConfig;
  scalingConfig: ScalingConfig;
  securityConfig: SecurityConfig;
  costConfig: CostConfig;
  sloConfig: SloConfig;
  chaosConfig: ChaosConfig;
}

export interface DeploymentConfig {
  cicdProvider: 'github-actions' | 'gitlab-ci' | 'jenkins' | 'tekton';
  environments: string[];
  rolloutStrategy: 'blue-green' | 'canary' | 'rolling';
  healthCheckUrl: string;
  timeoutSeconds: number;
}

export interface MonitoringConfig {
  metricsEndpoint: string;
  logsEndpoint: string;
  tracesEndpoint: string;
  healthEndpoints: string[];
  checkIntervalMs: number;
}

export interface AlertingConfig {
  channels: AlertChannel[];
  thresholds: AlertThreshold[];
  escalationPolicy: EscalationPolicy[];
}

export interface AlertChannel {
  type: 'slack' | 'email' | 'pagerduty' | 'webhook';
  endpoint: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
}

export interface AlertThreshold {
  metric: string;
  condition: 'gt' | 'lt' | 'eq';
  value: number;
  duration: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
}

export interface EscalationPolicy {
  delay: string;
  channels: string[];
}

export interface ScalingConfig {
  minInstances: number;
  maxInstances: number;
  targetCpuPercent: number;
  targetMemoryPercent: number;
  scaleUpCooldown: string;
  scaleDownCooldown: string;
}

export interface SecurityConfig {
  scanSchedule: string;
  vulnerabilityThreshold: 'low' | 'medium' | 'high' | 'critical';
  complianceFrameworks: string[];
  securityEndpoints: string[];
}

export interface CostConfig {
  budgetLimit: number;
  costCenter: string;
  optimizationTargets: string[];
  reportingSchedule: string;
}

export interface SloConfig {
  availability: number; // e.g., 99.9
  latencyP95Ms: number;
  errorRatePercent: number;
  throughputRps: number;
  evaluationWindow: string;
}

export interface ChaosConfig {
  enabled: boolean;
  schedule: string;
  experiments: ChaosExperiment[];
  safetyLimits: SafetyLimits;
}

export interface ChaosExperiment {
  name: string;
  type: 'pod-failure' | 'network-latency' | 'cpu-stress' | 'memory-stress';
  targets: string[];
  duration: string;
  intensity: number;
}

export interface SafetyLimits {
  maxErrorRate: number;
  maxLatencyMs: number;
  minHealthyInstances: number;
}

// Zod schemas for validation
export const DeploymentConfigSchema = z.object({
  cicdProvider: z.enum(['github-actions', 'gitlab-ci', 'jenkins', 'tekton']),
  environments: z.array(z.string()),
  rolloutStrategy: z.enum(['blue-green', 'canary', 'rolling']),
  healthCheckUrl: z.string().url(),
  timeoutSeconds: z.number().positive(),
});

export const MonitoringConfigSchema = z.object({
  metricsEndpoint: z.string().url(),
  logsEndpoint: z.string().url(),
  tracesEndpoint: z.string().url(),
  healthEndpoints: z.array(z.string().url()),
  checkIntervalMs: z.number().positive(),
});

export const AlertingConfigSchema = z.object({
  channels: z.array(z.object({
    type: z.enum(['slack', 'email', 'pagerduty', 'webhook']),
    endpoint: z.string(),
    severity: z.enum(['low', 'medium', 'high', 'critical']),
  })),
  thresholds: z.array(z.object({
    metric: z.string(),
    condition: z.enum(['gt', 'lt', 'eq']),
    value: z.number(),
    duration: z.string(),
    severity: z.enum(['low', 'medium', 'high', 'critical']),
  })),
  escalationPolicy: z.array(z.object({
    delay: z.string(),
    channels: z.array(z.string()),
  })),
});

export const ScalingConfigSchema = z.object({
  minInstances: z.number().int().positive(),
  maxInstances: z.number().int().positive(),
  targetCpuPercent: z.number().min(1).max(100),
  targetMemoryPercent: z.number().min(1).max(100),
  scaleUpCooldown: z.string(),
  scaleDownCooldown: z.string(),
});

export const SecurityConfigSchema = z.object({
  scanSchedule: z.string(),
  vulnerabilityThreshold: z.enum(['low', 'medium', 'high', 'critical']),
  complianceFrameworks: z.array(z.string()),
  securityEndpoints: z.array(z.string().url()),
});

export const CostConfigSchema = z.object({
  budgetLimit: z.number().positive(),
  costCenter: z.string(),
  optimizationTargets: z.array(z.string()),
  reportingSchedule: z.string(),
});

export const SloConfigSchema = z.object({
  availability: z.number().min(0).max(100),
  latencyP95Ms: z.number().positive(),
  errorRatePercent: z.number().min(0).max(100),
  throughputRps: z.number().positive(),
  evaluationWindow: z.string(),
});

export const ChaosConfigSchema = z.object({
  enabled: z.boolean(),
  schedule: z.string(),
  experiments: z.array(z.object({
    name: z.string(),
    type: z.enum(['pod-failure', 'network-latency', 'cpu-stress', 'memory-stress']),
    targets: z.array(z.string()),
    duration: z.string(),
    intensity: z.number().min(0).max(100),
  })),
  safetyLimits: z.object({
    maxErrorRate: z.number().min(0).max(100),
    maxLatencyMs: z.number().positive(),
    minHealthyInstances: z.number().int().positive(),
  }),
});

export const OperateAgentConfigSchema = z.object({
  deploymentConfig: DeploymentConfigSchema,
  monitoringConfig: MonitoringConfigSchema,
  alertingConfig: AlertingConfigSchema,
  scalingConfig: ScalingConfigSchema,
  securityConfig: SecurityConfigSchema,
  costConfig: CostConfigSchema,
  sloConfig: SloConfigSchema,
  chaosConfig: ChaosConfigSchema,
});

// Core Operate Agent class
export class OperateAgent {
  private logger: pino.Logger;
  private config: OperateAgentConfig;
  private deploymentHistory: DeploymentRecord[] = [];
  private incidentHistory: IncidentRecord[] = [];
  private performanceMetrics: PerformanceMetrics = {};
  private costMetrics: CostMetrics = {};

  constructor(config: OperateAgentConfig) {
    this.config = OperateAgentConfigSchema.parse(config);
    this.logger = pino({ name: 'operate-agent' });
  }

  // Deployment orchestration
  async deployApplication(params: DeploymentParams): Promise<DeploymentResult> {
    this.logger.info({ params }, 'Starting application deployment');
    
    try {
      const deploymentId = this.generateDeploymentId();
      const startTime = new Date();

      // Pre-deployment checks
      await this.runPreDeploymentChecks(params);
      
      // Execute deployment strategy
      const result = await this.executeDeploymentStrategy(deploymentId, params);
      
      // Post-deployment verification
      await this.verifyDeployment(deploymentId, params);
      
      const endTime = new Date();
      const record: DeploymentRecord = {
        id: deploymentId,
        environment: params.environment,
        version: params.version,
        strategy: params.strategy || this.config.deploymentConfig.rolloutStrategy,
        status: result.success ? 'success' : 'failed',
        startTime,
        endTime,
        duration: endTime.getTime() - startTime.getTime(),
        rollbackOnFailure: params.rollbackOnFailure || false,
      };
      
      this.deploymentHistory.push(record);
      
      this.logger.info({ deploymentId, result }, 'Deployment completed');
      return result;
      
    } catch (error) {
      this.logger.error({ error, params }, 'Deployment failed');
      throw error;
    }
  }

  // Health and monitoring
  async monitorHealth(): Promise<HealthStatus> {
    this.logger.debug('Checking system health');
    
    const healthChecks = await Promise.allSettled(
      this.config.monitoringConfig.healthEndpoints.map(endpoint => this.checkEndpointHealth(endpoint))
    );
    
    const overallStatus = healthChecks.every(check => 
      check.status === 'fulfilled' && check.value.healthy
    ) ? 'healthy' : 'unhealthy';
    
    const details = healthChecks.map((check, index) => ({
      endpoint: this.config.monitoringConfig.healthEndpoints[index],
      status: check.status === 'fulfilled' ? check.value : { healthy: false, error: 'Check failed' },
    }));
    
    const healthStatus: HealthStatus = {
      overall: overallStatus,
      timestamp: new Date(),
      details,
    };
    
    this.logger.info({ healthStatus }, 'Health check completed');
    return healthStatus;
  }

  // Log analysis
  async analyzeLogs(params: LogAnalysisParams): Promise<LogAnalysisResult> {
    this.logger.info({ params }, 'Starting log analysis');
    
    try {
      const logs = await this.fetchLogs(params);
      const analysis = await this.performLogAnalysis(logs, params);
      
      this.logger.info({ analysis }, 'Log analysis completed');
      return analysis;
      
    } catch (error) {
      this.logger.error({ error, params }, 'Log analysis failed');
      throw error;
    }
  }

  // Incident management
  async manageIncident(params: IncidentParams): Promise<IncidentResult> {
    this.logger.info({ params }, 'Managing incident');
    
    try {
      const incidentId = this.generateIncidentId();
      const startTime = new Date();
      
      let result: IncidentResult;
      
      switch (params.action) {
        case 'create':
          result = await this.createIncident(incidentId, params);
          break;
        case 'update':
          result = await this.updateIncident(params);
          break;
        case 'resolve':
          result = await this.resolveIncident(params);
          break;
        case 'escalate':
          result = await this.escalateIncident(params);
          break;
        default:
          throw new Error(`Unknown incident action: ${params.action}`);
      }
      
      if (params.action === 'create') {
        const record: IncidentRecord = {
          id: incidentId,
          title: params.title!,
          description: params.description!,
          severity: params.severity!,
          status: 'open',
          createdAt: startTime,
          updatedAt: startTime,
          assignee: params.assignee,
        };
        this.incidentHistory.push(record);
      }
      
      this.logger.info({ incidentId, result }, 'Incident management completed');
      return result;
      
    } catch (error) {
      this.logger.error({ error, params }, 'Incident management failed');
      throw error;
    }
  }

  // Performance optimization
  async optimizePerformance(params: PerformanceOptimizationParams): Promise<PerformanceOptimizationResult> {
    this.logger.info({ params }, 'Starting performance optimization');
    
    try {
      const metrics = await this.collectPerformanceMetrics(params);
      const recommendations = await this.generateOptimizationRecommendations(metrics, params);
      const appliedOptimizations = await this.applyOptimizations(recommendations, params);
      
      const result: PerformanceOptimizationResult = {
        metrics,
        recommendations,
        appliedOptimizations,
        timestamp: new Date(),
      };
      
      this.logger.info({ result }, 'Performance optimization completed');
      return result;
      
    } catch (error) {
      this.logger.error({ error, params }, 'Performance optimization failed');
      throw error;
    }
  }

  // Resource scaling
  async scaleResources(params: ScalingParams): Promise<ScalingResult> {
    this.logger.info({ params }, 'Scaling resources');
    
    try {
      const currentScale = await this.getCurrentScale(params.service);
      const targetScale = this.calculateTargetScale(params, currentScale);
      
      if (targetScale === currentScale.instances) {
        return {
          action: 'none',
          currentInstances: currentScale.instances,
          targetInstances: targetScale,
          message: 'No scaling required',
        };
      }
      
      const action = targetScale > currentScale.instances ? 'scale-up' : 'scale-down';
      await this.executeScaling(params.service, targetScale);
      
      const result: ScalingResult = {
        action,
        currentInstances: currentScale.instances,
        targetInstances: targetScale,
        message: `Scaled ${action} from ${currentScale.instances} to ${targetScale} instances`,
      };
      
      this.logger.info({ result }, 'Resource scaling completed');
      return result;
      
    } catch (error) {
      this.logger.error({ error, params }, 'Resource scaling failed');
      throw error;
    }
  }

  // Chaos engineering
  async runChaosTest(params: ChaosTestParams): Promise<ChaosTestResult> {
    this.logger.info({ params }, 'Running chaos test');
    
    if (!this.config.chaosConfig.enabled) {
      throw new Error('Chaos engineering is disabled');
    }
    
    try {
      const testId = this.generateChaosTestId();
      const startTime = new Date();
      
      // Safety checks
      await this.performChaosPreChecks();
      
      // Execute chaos experiment
      const experiment = this.config.chaosConfig.experiments.find(exp => exp.name === params.experiment);
      if (!experiment) {
        throw new Error(`Chaos experiment '${params.experiment}' not found`);
      }
      
      const result = await this.executeChaosExperiment(testId, experiment, params);
      
      const endTime = new Date();
      const testResult: ChaosTestResult = {
        testId,
        experiment: params.experiment,
        startTime,
        endTime,
        duration: endTime.getTime() - startTime.getTime(),
        success: result.success,
        impact: result.impact,
        observations: result.observations,
      };
      
      this.logger.info({ testResult }, 'Chaos test completed');
      return testResult;
      
    } catch (error) {
      this.logger.error({ error, params }, 'Chaos test failed');
      throw error;
    }
  }

  // SLO tracking
  async trackSlo(): Promise<SloStatus> {
    this.logger.debug('Tracking SLO compliance');
    
    try {
      const currentMetrics = await this.collectSloMetrics();
      const sloStatus = this.evaluateSloCompliance(currentMetrics);
      
      this.logger.info({ sloStatus }, 'SLO tracking completed');
      return sloStatus;
      
    } catch (error) {
      this.logger.error({ error }, 'SLO tracking failed');
      throw error;
    }
  }

  // Cost analysis
  async analyzeCosts(params: CostAnalysisParams): Promise<CostAnalysisResult> {
    this.logger.info({ params }, 'Analyzing costs');
    
    try {
      const currentCosts = await this.collectCostMetrics(params);
      const recommendations = await this.generateCostOptimizations(currentCosts, params);
      const projectedSavings = this.calculateProjectedSavings(recommendations);
      
      const result: CostAnalysisResult = {
        currentCosts,
        recommendations,
        projectedSavings,
        budgetStatus: this.evaluateBudgetStatus(currentCosts),
        timestamp: new Date(),
      };
      
      this.logger.info({ result }, 'Cost analysis completed');
      return result;
      
    } catch (error) {
      this.logger.error({ error, params }, 'Cost analysis failed');
      throw error;
    }
  }

  // Security scanning
  async securityScan(params: SecurityScanParams): Promise<SecurityScanResult> {
    this.logger.info({ params }, 'Running security scan');
    
    try {
      const scanId = this.generateSecurityScanId();
      const startTime = new Date();
      
      const vulnerabilities = await this.scanForVulnerabilities(params);
      const complianceStatus = await this.checkCompliance(params);
      const recommendations = this.generateSecurityRecommendations(vulnerabilities, complianceStatus);
      
      const endTime = new Date();
      const result: SecurityScanResult = {
        scanId,
        startTime,
        endTime,
        vulnerabilities,
        complianceStatus,
        recommendations,
        riskScore: this.calculateRiskScore(vulnerabilities),
      };
      
      this.logger.info({ result }, 'Security scan completed');
      return result;
      
    } catch (error) {
      this.logger.error({ error, params }, 'Security scan failed');
      throw error;
    }
  }

  // Private helper methods
  private generateDeploymentId(): string {
    return `deploy-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  }

  private generateIncidentId(): string {
    return `inc-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  }

  private generateChaosTestId(): string {
    return `chaos-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  }

  private generateSecurityScanId(): string {
    return `sec-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  }

  private async runPreDeploymentChecks(params: DeploymentParams): Promise<void> {
    // Implement pre-deployment validation logic
    this.logger.debug('Running pre-deployment checks');
  }

  private async executeDeploymentStrategy(deploymentId: string, params: DeploymentParams): Promise<DeploymentResult> {
    // Implement deployment strategy execution
    return {
      success: true,
      deploymentId,
      message: 'Deployment completed successfully',
    };
  }

  private async verifyDeployment(deploymentId: string, params: DeploymentParams): Promise<void> {
    // Implement post-deployment verification
    this.logger.debug({ deploymentId }, 'Verifying deployment');
  }

  private async checkEndpointHealth(endpoint: string): Promise<{ healthy: boolean; error?: string }> {
    try {
      // Implement actual health check logic
      return { healthy: true };
    } catch (error) {
      return { healthy: false, error: error instanceof Error ? error.message : 'Unknown error' };
    }
  }

  private async fetchLogs(params: LogAnalysisParams): Promise<LogEntry[]> {
    // Implement log fetching logic
    return [];
  }

  private async performLogAnalysis(logs: LogEntry[], params: LogAnalysisParams): Promise<LogAnalysisResult> {
    // Implement log analysis logic
    return {
      totalLogs: logs.length,
      errorLogs: 0,
      warningLogs: 0,
      patterns: [],
      anomalies: [],
      recommendations: [],
    };
  }

  private async createIncident(incidentId: string, params: IncidentParams): Promise<IncidentResult> {
    // Implement incident creation logic
    return {
      incidentId,
      action: 'created',
      message: 'Incident created successfully',
    };
  }

  private async updateIncident(params: IncidentParams): Promise<IncidentResult> {
    // Implement incident update logic
    return {
      incidentId: params.incidentId!,
      action: 'updated',
      message: 'Incident updated successfully',
    };
  }

  private async resolveIncident(params: IncidentParams): Promise<IncidentResult> {
    // Implement incident resolution logic
    return {
      incidentId: params.incidentId!,
      action: 'resolved',
      message: 'Incident resolved successfully',
    };
  }

  private async escalateIncident(params: IncidentParams): Promise<IncidentResult> {
    // Implement incident escalation logic
    return {
      incidentId: params.incidentId!,
      action: 'escalated',
      message: 'Incident escalated successfully',
    };
  }

  private async collectPerformanceMetrics(params: PerformanceOptimizationParams): Promise<PerformanceMetrics> {
    // Implement performance metrics collection
    return {};
  }

  private async generateOptimizationRecommendations(metrics: PerformanceMetrics, params: PerformanceOptimizationParams): Promise<OptimizationRecommendation[]> {
    // Implement optimization recommendation logic
    return [];
  }

  private async applyOptimizations(recommendations: OptimizationRecommendation[], params: PerformanceOptimizationParams): Promise<AppliedOptimization[]> {
    // Implement optimization application logic
    return [];
  }

  private async getCurrentScale(service: string): Promise<{ instances: number }> {
    // Implement current scale retrieval logic
    return { instances: 1 };
  }

  private calculateTargetScale(params: ScalingParams, currentScale: { instances: number }): number {
    // Implement target scale calculation logic
    return currentScale.instances;
  }

  private async executeScaling(service: string, targetInstances: number): Promise<void> {
    // Implement scaling execution logic
    this.logger.debug({ service, targetInstances }, 'Executing scaling');
  }

  private async performChaosPreChecks(): Promise<void> {
    // Implement chaos pre-checks
    this.logger.debug('Performing chaos pre-checks');
  }

  private async executeChaosExperiment(testId: string, experiment: ChaosExperiment, params: ChaosTestParams): Promise<{ success: boolean; impact: any; observations: any[] }> {
    // Implement chaos experiment execution
    return {
      success: true,
      impact: {},
      observations: [],
    };
  }

  private async collectSloMetrics(): Promise<any> {
    // Implement SLO metrics collection
    return {};
  }

  private evaluateSloCompliance(metrics: any): SloStatus {
    // Implement SLO compliance evaluation
    return {
      availability: { target: this.config.sloConfig.availability, actual: 99.9, compliant: true },
      latency: { target: this.config.sloConfig.latencyP95Ms, actual: 100, compliant: true },
      errorRate: { target: this.config.sloConfig.errorRatePercent, actual: 0.1, compliant: true },
      throughput: { target: this.config.sloConfig.throughputRps, actual: 1000, compliant: true },
      timestamp: new Date(),
    };
  }

  private async collectCostMetrics(params: CostAnalysisParams): Promise<CostMetrics> {
    // Implement cost metrics collection
    return {};
  }

  private async generateCostOptimizations(costs: CostMetrics, params: CostAnalysisParams): Promise<CostOptimization[]> {
    // Implement cost optimization recommendations
    return [];
  }

  private calculateProjectedSavings(optimizations: CostOptimization[]): number {
    // Implement projected savings calculation
    return 0;
  }

  private evaluateBudgetStatus(costs: CostMetrics): 'under' | 'at' | 'over' {
    // Implement budget status evaluation
    return 'under';
  }

  private async scanForVulnerabilities(params: SecurityScanParams): Promise<Vulnerability[]> {
    // Implement vulnerability scanning
    return [];
  }

  private async checkCompliance(params: SecurityScanParams): Promise<ComplianceStatus> {
    // Implement compliance checking
    return {};
  }

  private generateSecurityRecommendations(vulnerabilities: Vulnerability[], complianceStatus: ComplianceStatus): SecurityRecommendation[] {
    // Implement security recommendations generation
    return [];
  }

  private calculateRiskScore(vulnerabilities: Vulnerability[]): number {
    // Implement risk score calculation
    return 0;
  }
}

// Type definitions for method parameters and results
export interface DeploymentParams {
  environment: string;
  version: string;
  strategy?: 'blue-green' | 'canary' | 'rolling';
  rollbackOnFailure?: boolean;
  healthCheckTimeout?: number;
}

export interface DeploymentResult {
  success: boolean;
  deploymentId: string;
  message: string;
  rollbackPerformed?: boolean;
}

export interface DeploymentRecord {
  id: string;
  environment: string;
  version: string;
  strategy: string;
  status: 'success' | 'failed' | 'rolled-back';
  startTime: Date;
  endTime: Date;
  duration: number;
  rollbackOnFailure: boolean;
}

export interface HealthStatus {
  overall: 'healthy' | 'unhealthy';
  timestamp: Date;
  details: Array<{
    endpoint: string;
    status: { healthy: boolean; error?: string };
  }>;
}

export interface LogAnalysisParams {
  startTime: Date;
  endTime: Date;
  logLevel?: 'debug' | 'info' | 'warn' | 'error';
  service?: string;
  query?: string;
}

export interface LogAnalysisResult {
  totalLogs: number;
  errorLogs: number;
  warningLogs: number;
  patterns: LogPattern[];
  anomalies: LogAnomaly[];
  recommendations: string[];
}

export interface LogEntry {
  timestamp: Date;
  level: string;
  message: string;
  service: string;
  metadata?: Record<string, any>;
}

export interface LogPattern {
  pattern: string;
  frequency: number;
  severity: string;
}

export interface LogAnomaly {
  type: string;
  description: string;
  severity: string;
  occurrences: number;
}

export interface IncidentParams {
  action: 'create' | 'update' | 'resolve' | 'escalate';
  incidentId?: string;
  title?: string;
  description?: string;
  severity?: 'low' | 'medium' | 'high' | 'critical';
  assignee?: string;
  updateNotes?: string;
  resolution?: string;
}

export interface IncidentResult {
  incidentId: string;
  action: string;
  message: string;
}

export interface IncidentRecord {
  id: string;
  title: string;
  description: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
  status: 'open' | 'assigned' | 'in-progress' | 'resolved' | 'closed';
  createdAt: Date;
  updatedAt: Date;
  assignee?: string;
  resolution?: string;
}

export interface PerformanceOptimizationParams {
  service?: string;
  timeWindow: string;
  metrics: string[];
  autoApply?: boolean;
}

export interface PerformanceOptimizationResult {
  metrics: PerformanceMetrics;
  recommendations: OptimizationRecommendation[];
  appliedOptimizations: AppliedOptimization[];
  timestamp: Date;
}

export interface PerformanceMetrics {
  [key: string]: any;
}

export interface OptimizationRecommendation {
  type: string;
  description: string;
  impact: 'low' | 'medium' | 'high';
  effort: 'low' | 'medium' | 'high';
  estimatedImprovement: string;
}

export interface AppliedOptimization {
  recommendation: string;
  applied: boolean;
  result?: string;
  error?: string;
}

export interface ScalingParams {
  service: string;
  action?: 'auto' | 'scale-up' | 'scale-down';
  targetInstances?: number;
  force?: boolean;
}

export interface ScalingResult {
  action: 'scale-up' | 'scale-down' | 'none';
  currentInstances: number;
  targetInstances: number;
  message: string;
}

export interface ChaosTestParams {
  experiment: string;
  dryRun?: boolean;
  duration?: string;
  intensity?: number;
}

export interface ChaosTestResult {
  testId: string;
  experiment: string;
  startTime: Date;
  endTime: Date;
  duration: number;
  success: boolean;
  impact: any;
  observations: any[];
}

export interface SloStatus {
  availability: { target: number; actual: number; compliant: boolean };
  latency: { target: number; actual: number; compliant: boolean };
  errorRate: { target: number; actual: number; compliant: boolean };
  throughput: { target: number; actual: number; compliant: boolean };
  timestamp: Date;
}

export interface CostAnalysisParams {
  timeWindow: string;
  services?: string[];
  includePredictions?: boolean;
}

export interface CostAnalysisResult {
  currentCosts: CostMetrics;
  recommendations: CostOptimization[];
  projectedSavings: number;
  budgetStatus: 'under' | 'at' | 'over';
  timestamp: Date;
}

export interface CostMetrics {
  [key: string]: any;
}

export interface CostOptimization {
  type: string;
  description: string;
  estimatedSavings: number;
  effort: 'low' | 'medium' | 'high';
  risk: 'low' | 'medium' | 'high';
}

export interface SecurityScanParams {
  scope?: 'infrastructure' | 'application' | 'dependencies' | 'all';
  includeCompliance?: boolean;
  frameworks?: string[];
}

export interface SecurityScanResult {
  scanId: string;
  startTime: Date;
  endTime: Date;
  vulnerabilities: Vulnerability[];
  complianceStatus: ComplianceStatus;
  recommendations: SecurityRecommendation[];
  riskScore: number;
}

export interface Vulnerability {
  id: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
  type: string;
  description: string;
  affected: string[];
  remediation?: string;
}

export interface ComplianceStatus {
  [framework: string]: {
    compliant: boolean;
    score: number;
    issues: string[];
  };
}

export interface SecurityRecommendation {
  type: string;
  description: string;
  priority: 'low' | 'medium' | 'high' | 'critical';
  effort: 'low' | 'medium' | 'high';
}