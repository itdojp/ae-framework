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
  duration?: number; // How long condition must be true
  aggregation?: 'avg' | 'min' | 'max' | 'sum' | 'count';
  timeWindow?: number; // Time window for aggregation
}

export interface NotificationConfig {
  type: 'email' | 'slack' | 'webhook' | 'console' | 'file';
  target: string; // email address, webhook URL, etc.
  template?: string;
  enabled: boolean;
  throttle?: number; // Minimum time between notifications
}

export interface EscalationConfig {
  levels: EscalationLevel[];
  autoResolve: boolean;
  maxEscalationTime: number;
}

export interface EscalationLevel {
  level: number;
  delay: number; // Time to wait before escalating
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

export class AlertManager extends EventEmitter {
  private rules = new Map<string, AlertRule>();
  private activeAlerts = new Map<string, AlertInstance>();
  private alertHistory: AlertHistory[] = [];
  private evaluationTimer?: NodeJS.Timeout;
  private metricBuffer = new Map<string, MetricPoint[]>();
  private notificationThrottles = new Map<string, Date>();
  private isRunning = false;
  
  private readonly maxHistorySize = 10000;
  private readonly maxMetricBufferSize = 1000;
  private readonly defaultEvaluationInterval = 30000; // 30 seconds

  constructor() {
    super();
    this.setupDefaultRules();
  }

  /**
   * Start alert manager
   */
  start(): void {
    if (this.isRunning) {
      return;
    }

    this.isRunning = true;
    this.startEvaluation();
    this.emit('alertManagerStarted');
    console.log('🚨 Alert Manager started');
  }

  /**
   * Stop alert manager
   */
  stop(): void {
    if (!this.isRunning) {
      return;
    }

    this.isRunning = false;
    
    if (this.evaluationTimer) {
      clearInterval(this.evaluationTimer);
      this.evaluationTimer = undefined;
    }

    this.emit('alertManagerStopped');
    console.log('🚨 Alert Manager stopped');
  }

  /**
   * Add alert rule
   */
  addRule(rule: AlertRule): void {
    this.rules.set(rule.id, rule);
    this.emit('ruleAdded', rule);
    console.log(`📋 Added alert rule: ${rule.name}`);
  }

  /**
   * Update alert rule
   */
  updateRule(ruleId: string, updates: Partial<AlertRule>): void {
    const rule = this.rules.get(ruleId);
    if (!rule) {
      throw new Error(`Alert rule not found: ${ruleId}`);
    }

    const updatedRule = { ...rule, ...updates };
    this.rules.set(ruleId, updatedRule);
    this.emit('ruleUpdated', updatedRule);
  }

  /**
   * Remove alert rule
   */
  removeRule(ruleId: string): void {
    const rule = this.rules.get(ruleId);
    if (!rule) {
      throw new Error(`Alert rule not found: ${ruleId}`);
    }

    this.rules.delete(ruleId);
    
    // Resolve any active alerts for this rule
    for (const [alertId, alert] of this.activeAlerts) {
      if (alert.ruleId === ruleId) {
        this.resolveAlert(alertId, 'Rule removed');
      }
    }

    this.emit('ruleRemoved', rule);
  }

  /**
   * Process metric point for alert evaluation
   */
  processMetric(metric: MetricPoint): void {
    if (!this.metricBuffer.has(metric.name)) {
      this.metricBuffer.set(metric.name, []);
    }

    const buffer = this.metricBuffer.get(metric.name)!;
    buffer.push(metric);

    // Limit buffer size
    if (buffer.length > this.maxMetricBufferSize) {
      buffer.splice(0, buffer.length - this.maxMetricBufferSize);
    }

    // Immediate evaluation for critical metrics
    this.evaluateRulesForMetric(metric.name);
  }

  /**
   * Process performance alert from monitor
   */
  processPerformanceAlert(perfAlert: PerformanceAlert): void {
    const alertInstance: AlertInstance = {
      id: perfAlert.id,
      ruleId: 'performance-monitor',
      ruleName: 'Performance Monitor Alert',
      status: 'firing',
      severity: perfAlert.type === 'critical' ? 'critical' : 'warning',
      message: perfAlert.message,
      metric: perfAlert.category,
      currentValue: perfAlert.currentValue,
      threshold: perfAlert.threshold,
      startTime: perfAlert.timestamp,
      duration: 0,
      escalationLevel: 0,
      notificationsSent: 0,
      labels: {
        source: 'performance-monitor',
        category: perfAlert.category
      },
      annotations: {
        recommendations: perfAlert.recommendations.join(', ')
      }
    };

    this.fireAlert(alertInstance);
  }

  /**
   * Silence alert
   */
  silenceAlert(alertId: string, duration: number): void {
    const alert = this.activeAlerts.get(alertId);
    if (!alert) {
      throw new Error(`Alert not found: ${alertId}`);
    }

    alert.status = 'silenced';
    
    const rule = this.rules.get(alert.ruleId);
    if (rule) {
      rule.silenced = true;
      rule.silenceUntil = new Date(Date.now() + duration);
    }

    this.addHistory(alertId, 'silenced', { duration });
    this.emit('alertSilenced', alert);
  }

  /**
   * Unsilence alert
   */
  unsilenceAlert(alertId: string): void {
    const alert = this.activeAlerts.get(alertId);
    if (!alert) {
      throw new Error(`Alert not found: ${alertId}`);
    }

    if (alert.status === 'silenced') {
      alert.status = 'firing';
    }

    const rule = this.rules.get(alert.ruleId);
    if (rule) {
      rule.silenced = false;
      rule.silenceUntil = undefined;
    }

    this.emit('alertUnsilenced', alert);
  }

  /**
   * Get alert summary
   */
  getAlertSummary(): AlertSummary {
    const alerts = Array.from(this.activeAlerts.values());
    
    const summary: AlertSummary = {
      total: alerts.length,
      firing: alerts.filter(a => a.status === 'firing').length,
      resolved: alerts.filter(a => a.status === 'resolved').length,
      silenced: alerts.filter(a => a.status === 'silenced').length,
      bySeverity: {
        info: alerts.filter(a => a.severity === 'info').length,
        warning: alerts.filter(a => a.severity === 'warning').length,
        critical: alerts.filter(a => a.severity === 'critical').length
      },
      byMetric: {},
      recentActivity: this.alertHistory.slice(-20)
    };

    // Count by metric
    for (const alert of alerts) {
      summary.byMetric[alert.metric] = (summary.byMetric[alert.metric] || 0) + 1;
    }

    return summary;
  }

  /**
   * Get active alerts
   */
  getActiveAlerts(): AlertInstance[] {
    return Array.from(this.activeAlerts.values())
      .filter(a => a.status === 'firing')
      .sort((a, b) => {
        // Sort by severity (critical first), then by start time
        const severityOrder = { critical: 0, warning: 1, info: 2 };
        const severityDiff = severityOrder[a.severity] - severityOrder[b.severity];
        return severityDiff || b.startTime.getTime() - a.startTime.getTime();
      });
  }

  /**
   * Get alert history
   */
  getAlertHistory(limit = 100): AlertHistory[] {
    return this.alertHistory.slice(-limit);
  }

  /**
   * Clear resolved alerts
   */
  clearResolvedAlerts(): void {
    const resolvedCount = Array.from(this.activeAlerts.values())
      .filter(a => a.status === 'resolved').length;

    for (const [alertId, alert] of this.activeAlerts) {
      if (alert.status === 'resolved') {
        this.activeAlerts.delete(alertId);
      }
    }

    this.emit('resolvedAlertsCleared', { count: resolvedCount });
  }

  // Private methods
  private setupDefaultRules(): void {
    // High CPU usage rule
    this.addRule({
      id: 'high-cpu-usage',
      name: 'High CPU Usage',
      description: 'Alert when CPU usage is consistently high',
      metric: 'cpu.total',
      condition: {
        operator: 'gt',
        threshold: 80,
        duration: 300000, // 5 minutes
        aggregation: 'avg',
        timeWindow: 60000 // 1 minute window
      },
      severity: 'warning',
      enabled: true,
      silenced: false,
      evaluationInterval: 60000,
      notifications: [
        {
          type: 'console',
          target: '',
          enabled: true,
          throttle: 300000 // 5 minutes
        }
      ],
      tags: { category: 'performance', component: 'cpu' }
    });

    // Critical memory usage rule
    this.addRule({
      id: 'critical-memory-usage',
      name: 'Critical Memory Usage',
      description: 'Alert when memory usage exceeds critical threshold',
      metric: 'memory.usage_percent',
      condition: {
        operator: 'gt',
        threshold: 90,
        duration: 60000 // 1 minute
      },
      severity: 'critical',
      enabled: true,
      silenced: false,
      evaluationInterval: 30000,
      notifications: [
        {
          type: 'console',
          target: '',
          enabled: true
        }
      ],
      escalation: {
        levels: [
          {
            level: 1,
            delay: 300000, // 5 minutes
            notifications: [
              {
                type: 'console',
                target: '',
                enabled: true
              }
            ]
          }
        ],
        autoResolve: false,
        maxEscalationTime: 1800000 // 30 minutes
      },
      tags: { category: 'performance', component: 'memory' }
    });

    // High error rate rule
    this.addRule({
      id: 'high-error-rate',
      name: 'High Error Rate',
      description: 'Alert when error rate is too high',
      metric: 'errors.rate',
      condition: {
        operator: 'gt',
        threshold: 5,
        duration: 180000, // 3 minutes
        aggregation: 'avg'
      },
      severity: 'warning',
      enabled: true,
      silenced: false,
      evaluationInterval: 60000,
      notifications: [
        {
          type: 'console',
          target: '',
          enabled: true,
          throttle: 600000 // 10 minutes
        }
      ],
      tags: { category: 'reliability', component: 'errors' }
    });
  }

  private startEvaluation(): void {
    this.evaluationTimer = setInterval(() => {
      this.evaluateAllRules();
    }, this.defaultEvaluationInterval);
  }

  private evaluateAllRules(): void {
    for (const rule of this.rules.values()) {
      if (!rule.enabled || rule.silenced) {
        continue;
      }

      this.evaluateRule(rule);
    }

    this.updateAlertDurations();
    this.checkEscalations();
  }

  private evaluateRulesForMetric(metricName: string): void {
    for (const rule of this.rules.values()) {
      if (rule.metric === metricName && rule.enabled && !rule.silenced) {
        this.evaluateRule(rule);
      }
    }
  }

  private evaluateRule(rule: AlertRule): void {
    const buffer = this.metricBuffer.get(rule.metric);
    if (!buffer || buffer.length === 0) {
      return;
    }

    const now = Date.now();
    const timeWindow = rule.condition.timeWindow || rule.evaluationInterval;
    const windowStart = now - timeWindow;

    // Get metrics within time window
    const windowMetrics = buffer.filter(
      m => m.timestamp.getTime() >= windowStart
    );

    if (windowMetrics.length === 0) {
      return;
    }

    // Calculate aggregated value
    const values = windowMetrics.map(m => m.value);
    const aggregatedValue = this.calculateAggregation(values, rule.condition.aggregation || 'avg');

    // Check condition
    const conditionMet = this.evaluateCondition(aggregatedValue, rule.condition);

    const existingAlert = this.findAlertByRule(rule.id);

    if (conditionMet) {
      if (existingAlert) {
        // Update existing alert
        existingAlert.currentValue = aggregatedValue;
        this.emit('alertUpdated', existingAlert);
      } else {
        // Create new alert if condition duration is met
        if (this.isConditionDurationMet(rule, windowMetrics)) {
          this.createAlert(rule, aggregatedValue);
        }
      }
    } else if (existingAlert && existingAlert.status === 'firing') {
      // Resolve alert
      this.resolveAlert(existingAlert.id, 'Condition no longer met');
    }
  }

  private evaluateCondition(value: number, condition: AlertCondition): boolean {
    switch (condition.operator) {
      case 'gt': return value > condition.threshold;
      case 'gte': return value >= condition.threshold;
      case 'lt': return value < condition.threshold;
      case 'lte': return value <= condition.threshold;
      case 'eq': return value === condition.threshold;
      case 'ne': return value !== condition.threshold;
      default: return false;
    }
  }

  private isConditionDurationMet(rule: AlertRule, metrics: MetricPoint[]): boolean {
    if (!rule.condition.duration) {
      return true;
    }

    const now = Date.now();
    const durationStart = now - rule.condition.duration;

    // Check if condition has been met for the required duration
    const durationMetrics = metrics.filter(
      m => m.timestamp.getTime() >= durationStart
    );

    return durationMetrics.length > 0 && 
           durationMetrics.every(m => 
             this.evaluateCondition(m.value, rule.condition)
           );
  }

  private createAlert(rule: AlertRule, currentValue: number): void {
    const alertId = `alert-${rule.id}-${Date.now()}`;
    
    const alert: AlertInstance = {
      id: alertId,
      ruleId: rule.id,
      ruleName: rule.name,
      status: 'firing',
      severity: rule.severity,
      message: `${rule.name}: ${rule.metric} is ${currentValue} (threshold: ${rule.condition.threshold})`,
      metric: rule.metric,
      currentValue,
      threshold: rule.condition.threshold,
      startTime: new Date(),
      duration: 0,
      escalationLevel: 0,
      notificationsSent: 0,
      labels: { ...rule.tags },
      annotations: {
        description: rule.description,
        operator: rule.condition.operator,
        threshold: rule.condition.threshold.toString()
      }
    };

    this.fireAlert(alert);
  }

  private fireAlert(alert: AlertInstance): void {
    this.activeAlerts.set(alert.id, alert);
    this.addHistory(alert.id, 'fired', { 
      metric: alert.metric,
      value: alert.currentValue,
      threshold: alert.threshold
    });

    this.sendNotifications(alert);
    this.emit('alertFired', alert);
    
    console.warn(`🚨 Alert fired: ${alert.message}`);
  }

  private resolveAlert(alertId: string, reason: string): void {
    const alert = this.activeAlerts.get(alertId);
    if (!alert) {
      return;
    }

    alert.status = 'resolved';
    alert.endTime = new Date();
    alert.duration = alert.endTime.getTime() - alert.startTime.getTime();

    this.addHistory(alertId, 'resolved', { reason });
    this.emit('alertResolved', alert);
    
    console.log(`✅ Alert resolved: ${alert.message} (reason: ${reason})`);
  }

  private findAlertByRule(ruleId: string): AlertInstance | undefined {
    return Array.from(this.activeAlerts.values())
      .find(a => a.ruleId === ruleId && a.status === 'firing');
  }

  private updateAlertDurations(): void {
    const now = Date.now();
    
    for (const alert of this.activeAlerts.values()) {
      if (alert.status === 'firing') {
        alert.duration = now - alert.startTime.getTime();
      }
    }
  }

  private checkEscalations(): void {
    for (const alert of this.activeAlerts.values()) {
      if (alert.status !== 'firing') {
        continue;
      }

      const rule = this.rules.get(alert.ruleId);
      if (!rule?.escalation) {
        continue;
      }

      const nextLevel = alert.escalationLevel + 1;
      const escalationLevel = rule.escalation.levels.find(l => l.level === nextLevel);
      
      if (!escalationLevel) {
        continue;
      }

      if (alert.duration >= escalationLevel.delay) {
        this.escalateAlert(alert, escalationLevel);
      }
    }
  }

  private escalateAlert(alert: AlertInstance, escalationLevel: EscalationLevel): void {
    alert.escalationLevel = escalationLevel.level;
    
    this.addHistory(alert.id, 'escalated', { 
      level: escalationLevel.level 
    });

    // Send escalation notifications
    for (const notification of escalationLevel.notifications) {
      if (notification.enabled) {
        this.sendNotification(alert, notification, true);
      }
    }

    // Execute auto action if configured
    if (escalationLevel.autoAction) {
      this.executeAutoAction(alert, escalationLevel.autoAction);
    }

    this.emit('alertEscalated', alert);
    console.warn(`🔺 Alert escalated to level ${escalationLevel.level}: ${alert.message}`);
  }

  private sendNotifications(alert: AlertInstance): void {
    const rule = this.rules.get(alert.ruleId);
    if (!rule) {
      return;
    }

    for (const notification of rule.notifications) {
      if (notification.enabled) {
        this.sendNotification(alert, notification, false);
      }
    }
  }

  private sendNotification(
    alert: AlertInstance, 
    notification: NotificationConfig, 
    isEscalation: boolean
  ): void {
    const throttleKey = `${alert.id}-${notification.type}-${notification.target}`;
    const lastSent = this.notificationThrottles.get(throttleKey);
    
    if (lastSent && notification.throttle) {
      const timeSinceLastSent = Date.now() - lastSent.getTime();
      if (timeSinceLastSent < notification.throttle) {
        return;
      }
    }

    this.notificationThrottles.set(throttleKey, new Date());
    alert.notificationsSent++;

    this.addHistory(alert.id, 'notification_sent', {
      type: notification.type,
      target: notification.target,
      isEscalation
    });

    // Send notification based on type
    switch (notification.type) {
      case 'console':
        this.sendConsoleNotification(alert, isEscalation);
        break;
      case 'file':
        this.sendFileNotification(alert, notification.target, isEscalation);
        break;
      // Other notification types would be implemented here
    }

    this.emit('notificationSent', { alert, notification, isEscalation });
  }

  private sendConsoleNotification(alert: AlertInstance, isEscalation: boolean): void {
    const prefix = isEscalation ? '🔺 ESCALATED' : '🚨';
    const severity = alert.severity.toUpperCase();
    console.warn(`${prefix} [${severity}] ${alert.message}`);
  }

  private sendFileNotification(alert: AlertInstance, filePath: string, isEscalation: boolean): void {
    // Simplified file notification
    const message = {
      timestamp: new Date().toISOString(),
      alert_id: alert.id,
      severity: alert.severity,
      message: alert.message,
      metric: alert.metric,
      current_value: alert.currentValue,
      threshold: alert.threshold,
      is_escalation: isEscalation
    };

    // In a real implementation, this would write to the specified file
    console.log(`📄 File notification: ${JSON.stringify(message)}`);
  }

  private executeAutoAction(alert: AlertInstance, action: AutoAction): void {
    console.log(`🤖 Executing auto action: ${action.type} for alert ${alert.id}`);
    
    // Auto action implementations would go here
    switch (action.type) {
      case 'restart':
        console.log('🔄 Auto action: restart triggered');
        break;
      case 'scale':
        console.log('📈 Auto action: scale triggered');
        break;
      case 'cleanup':
        console.log('🧹 Auto action: cleanup triggered');
        break;
      case 'custom':
        console.log(`⚙️ Auto action: custom command - ${action.command}`);
        break;
    }
  }

  private addHistory(instanceId: string, action: AlertHistory['action'], details: Record<string, any>): void {
    const historyEntry: AlertHistory = {
      instanceId,
      action,
      timestamp: new Date(),
      details
    };

    this.alertHistory.push(historyEntry);

    // Limit history size
    if (this.alertHistory.length > this.maxHistorySize) {
      this.alertHistory = this.alertHistory.slice(-this.maxHistorySize / 2);
    }
  }

  private calculateAggregation(values: number[], aggregation: string): number {
    if (values.length === 0) return 0;

    switch (aggregation) {
      case 'avg':
        return values.reduce((sum, val) => sum + val, 0) / values.length;
      case 'min':
        return Math.min(...values);
      case 'max':
        return Math.max(...values);
      case 'sum':
        return values.reduce((sum, val) => sum + val, 0);
      case 'count':
        return values.length;
      default:
        return values[values.length - 1]; // Latest value
    }
  }
}