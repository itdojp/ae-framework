/**
 * Alert Manager for Phase 3.3 Optimization
 * Manages alerts, notifications, and escalation workflows
 */
import { EventEmitter } from 'events';
import type { PerformanceAlert } from './performance-monitor.js';
import type { MetricPoint } from './metrics-collector.js';
export interface AlertRule {
    id: string;
    name: string;
    description: string;
    metric: string;
    condition: AlertCondition;
    severity: 'info' | 'warning' | 'critical';
    enabled: boolean;
    silenced: boolean;
    silenceUntil?: Date;
    evaluationInterval: number;
    notifications: NotificationConfig[];
    escalation?: EscalationConfig;
    tags: Record<string, string>;
}
export interface AlertCondition {
    operator: 'gt' | 'gte' | 'lt' | 'lte' | 'eq' | 'ne';
    threshold: number;
    duration?: number;
    aggregation?: 'avg' | 'min' | 'max' | 'sum' | 'count';
    timeWindow?: number;
}
export interface NotificationConfig {
    type: 'email' | 'slack' | 'webhook' | 'console' | 'file';
    target: string;
    template?: string;
    enabled: boolean;
    throttle?: number;
}
export interface EscalationConfig {
    levels: EscalationLevel[];
    autoResolve: boolean;
    maxEscalationTime: number;
}
export interface EscalationLevel {
    level: number;
    delay: number;
    notifications: NotificationConfig[];
    autoAction?: AutoAction;
}
export interface AutoAction {
    type: 'restart' | 'scale' | 'cleanup' | 'custom';
    command?: string;
    parameters?: Record<string, any>;
}
export interface AlertInstance {
    id: string;
    ruleId: string;
    ruleName: string;
    status: 'firing' | 'resolved' | 'silenced';
    severity: AlertRule['severity'];
    message: string;
    metric: string;
    currentValue: number;
    threshold: number;
    startTime: Date;
    endTime?: Date;
    duration: number;
    escalationLevel: number;
    notificationsSent: number;
    labels: Record<string, string>;
    annotations: Record<string, string>;
}
export interface AlertHistory {
    instanceId: string;
    action: 'fired' | 'resolved' | 'escalated' | 'silenced' | 'notification_sent';
    timestamp: Date;
    details: Record<string, any>;
}
export interface AlertSummary {
    total: number;
    firing: number;
    resolved: number;
    silenced: number;
    bySeverity: {
        info: number;
        warning: number;
        critical: number;
    };
    byMetric: Record<string, number>;
    recentActivity: AlertHistory[];
}
export declare class AlertManager extends EventEmitter {
    private rules;
    private activeAlerts;
    private alertHistory;
    private evaluationTimer?;
    private metricBuffer;
    private notificationThrottles;
    private isRunning;
    private readonly maxHistorySize;
    private readonly maxMetricBufferSize;
    private readonly defaultEvaluationInterval;
    constructor();
    /**
     * Start alert manager
     */
    start(): void;
    /**
     * Stop alert manager
     */
    stop(): void;
    /**
     * Add alert rule
     */
    addRule(rule: AlertRule): void;
    /**
     * Update alert rule
     */
    updateRule(ruleId: string, updates: Partial<AlertRule>): void;
    /**
     * Remove alert rule
     */
    removeRule(ruleId: string): void;
    /**
     * Process metric point for alert evaluation
     */
    processMetric(metric: MetricPoint): void;
    /**
     * Process performance alert from monitor
     */
    processPerformanceAlert(perfAlert: PerformanceAlert): void;
    /**
     * Silence alert
     */
    silenceAlert(alertId: string, duration: number): void;
    /**
     * Unsilence alert
     */
    unsilenceAlert(alertId: string): void;
    /**
     * Get alert summary
     */
    getAlertSummary(): AlertSummary;
    /**
     * Get active alerts
     */
    getActiveAlerts(): AlertInstance[];
    /**
     * Get alert history
     */
    getAlertHistory(limit?: number): AlertHistory[];
    /**
     * Clear resolved alerts
     */
    clearResolvedAlerts(): void;
    private setupDefaultRules;
    private startEvaluation;
    private evaluateAllRules;
    private evaluateRulesForMetric;
    private evaluateRule;
    private evaluateCondition;
    private isConditionDurationMet;
    private createAlert;
    private fireAlert;
    private resolveAlert;
    private findAlertByRule;
    private updateAlertDurations;
    private checkEscalations;
    private escalateAlert;
    private sendNotifications;
    private sendNotification;
    private sendConsoleNotification;
    private sendFileNotification;
    private executeAutoAction;
    private addHistory;
    private calculateAggregation;
}
