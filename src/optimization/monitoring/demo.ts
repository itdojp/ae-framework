#!/usr/bin/env tsx
/**
 * Phase 3.3 Monitoring System Demo
 * Demonstrates the performance monitoring, metrics collection, and alerting capabilities
 */

import { MonitoringSystem } from './index.js';

async function runMonitoringDemo(): Promise<void> {
  console.log('🚀 Phase 3.3 Monitoring System Demo');
  console.log('=====================================\n');

  // Create monitoring system with demo configuration
  const monitoringSystem = new MonitoringSystem({
    performanceMonitor: {
      interval: 2000, // 2 seconds for demo
      thresholds: {
        cpu: { warning: 30, critical: 60 }, // Lower thresholds for demo
        memory: { warning: 40, critical: 70 },
        responseTime: { warning: 200, critical: 500 },
        errorRate: { warning: 2, critical: 5 }
      }
    },
    metricsCollector: {
      aggregationInterval: 5000, // 5 seconds
      retention: 300000 // 5 minutes
    },
    integration: {
      autoStart: false,
      exportMetrics: true,
      exportInterval: 10000 // 10 seconds
    }
  });

  // Set up event listeners
  setupEventListeners(monitoringSystem);

  try {
    // Start the monitoring system
    console.log('🔄 Starting monitoring system...');
    await monitoringSystem.start();
    console.log('✅ Monitoring system started\n');

    // Wait a moment for initial metrics
    await sleep(3000);

    // Demonstrate tracking operations
    console.log('📊 Demonstrating operation tracking...');
    await simulateOperations(monitoringSystem);

    // Demonstrate error tracking
    console.log('\n❌ Demonstrating error tracking...');
    simulateErrors(monitoringSystem);

    // Demonstrate custom metrics
    console.log('\n📈 Demonstrating custom metrics...');
    simulateCustomMetrics(monitoringSystem);

    // Wait for metrics to be collected
    await sleep(5000);

    // Show dashboard
    console.log('\n📋 Current Dashboard:');
    showDashboard(monitoringSystem);

    // Demonstrate alert triggering
    console.log('\n🚨 Demonstrating alert triggers...');
    await simulateHighLoad(monitoringSystem);

    // Wait for alerts to process
    await sleep(3000);

    // Show alerts
    console.log('\n🔔 Active Alerts:');
    showActiveAlerts(monitoringSystem);

    // Export metrics
    console.log('\n📤 Exporting metrics...');
    exportMetrics(monitoringSystem);

    // Run for a bit longer to show ongoing monitoring
    console.log('\n⏱️  Running monitoring for 30 seconds...');
    console.log('   (Watch for real-time metrics and alerts)');
    
    for (let i = 0; i < 30; i++) {
      // Simulate varying load
      if (i % 10 === 0) {
        await simulateOperations(monitoringSystem, 5);
      }
      
      if (i % 15 === 0) {
        simulateErrors(monitoringSystem, 2);
      }
      
      await sleep(1000);
      process.stdout.write('.');
    }
    
    console.log('\n\n📊 Final System Status:');
    showSystemHealth(monitoringSystem);

  } catch (error) {
    console.error('❌ Demo error:', error);
  } finally {
    console.log('\n🛑 Stopping monitoring system...');
    await monitoringSystem.stop();
    console.log('✅ Demo completed\n');
  }
}

function setupEventListeners(system: MonitoringSystem): void {
  system.on('systemStarted', () => {
    console.log('🟢 System started');
  });

  system.on('metricsUpdated', (metrics) => {
    if (Math.random() < 0.1) { // Show 10% of metrics updates
      console.log(`📊 Metrics: CPU ${metrics.cpuUsage.totalUsage.toFixed(1)}%, ` +
                  `Memory ${metrics.memoryUsage.usagePercentage.toFixed(1)}%, ` +
                  `Response ${metrics.responseTime.average.toFixed(0)}ms`);
    }
  });

  system.on('alertFired', (alert) => {
    const icon = alert.severity === 'critical' ? '🚨' : 
                 alert.severity === 'warning' ? '⚠️' : 'ℹ️';
    console.log(`${icon} ALERT [${alert.severity.toUpperCase()}]: ${alert.message}`);
  });

  system.on('alertResolved', (alert) => {
    console.log(`✅ RESOLVED: ${alert.message}`);
  });

  system.on('healthCheck', (health) => {
    if (health.overall === 'critical') {
      console.log('💔 System health: CRITICAL');
    } else if (health.overall === 'degraded') {
      console.log('💛 System health: DEGRADED');
    }
  });

  system.on('componentError', ({ component, error }) => {
    console.log(`❌ Component error in ${component}:`, error.message);
  });
}

async function simulateOperations(
  system: MonitoringSystem, 
  count: number = 10
): Promise<void> {
  for (let i = 0; i < count; i++) {
    const startTime = performance.now();
    
    // Simulate different operation types with varying durations
    const operationTypes = ['database_query', 'api_call', 'file_processing', 'computation'] as const;
    const operationType = operationTypes[i % 4];
    const duration = Math.random() * 500 + 50; // 50-550ms
    
    await sleep(duration);
    
    system.trackOperation(operationType, startTime);
    system.recordMetric(`operations.${operationType}.count`, 1, { 
      status: 'success',
      duration_bucket: duration < 100 ? 'fast' : duration < 300 ? 'medium' : 'slow'
    });
  }
  
  console.log(`   ✓ Tracked ${count} operations`);
}

function simulateErrors(system: MonitoringSystem, count: number = 3): void {
  const errorTypes = ['validation_error', 'network_timeout', 'database_error', 'permission_denied'];
  
  for (let i = 0; i < count; i++) {
    const errorType = errorTypes[i % errorTypes.length];
    system.trackError(errorType);
    system.recordMetric('errors.by_type', 1, { 
      type: errorType,
      severity: Math.random() < 0.3 ? 'high' : 'low'
    });
  }
  
  console.log(`   ✓ Tracked ${count} errors`);
}

function simulateCustomMetrics(system: MonitoringSystem): void {
  // Business metrics
  system.recordMetric('business.revenue', 15420.50, { currency: 'USD' });
  system.recordMetric('business.active_users', 1247, { period: 'current_hour' });
  system.recordMetric('business.conversion_rate', 3.2, { funnel: 'signup' });

  // Application metrics
  system.recordMetric('app.cache_hit_rate', 94.7, { cache_type: 'redis' });
  system.recordMetric('app.queue_size', 23, { queue_name: 'email_notifications' });
  system.recordMetric('app.connection_pool_usage', 67.3, { pool: 'database' });

  // Infrastructure metrics
  system.recordMetric('infra.disk_usage', 78.9, { mount: '/var/log' });
  system.recordMetric('infra.network_throughput', 125.6, { interface: 'eth0', direction: 'rx' });
  
  console.log('   ✓ Recorded custom business and infrastructure metrics');
}

async function simulateHighLoad(system: MonitoringSystem): Promise<void> {
  console.log('   🔥 Simulating high system load...');
  
  // Simulate high CPU operations
  for (let i = 0; i < 50; i++) {
    const startTime = performance.now();
    
    // CPU intensive operation simulation
    let result = 0;
    for (let j = 0; j < 100000; j++) {
      result += Math.sqrt(j);
    }
    
    system.trackOperation('cpu_intensive', startTime);
  }

  // Simulate high memory usage
  system.recordMetric('memory.usage_percent', 95.8);
  system.recordMetric('cpu.total', 87.5);

  // Simulate slow responses
  for (let i = 0; i < 10; i++) {
    const startTime = performance.now() - 2000; // Simulate 2 second operations
    system.trackOperation('slow_operation', startTime);
  }

  // Simulate error spike
  for (let i = 0; i < 20; i++) {
    system.trackError('overload_error');
  }

  console.log('   ✓ High load simulation completed');
}

function showDashboard(system: MonitoringSystem): void {
  const dashboard = system.getDashboard();
  
  console.log(`   Overall Health: ${getHealthIcon(dashboard.healthStatus.overall)} ${dashboard.healthStatus.overall.toUpperCase()}`);
  console.log(`   Uptime: ${formatDuration(dashboard.systemStats.uptime)}`);
  console.log(`   Total Metrics: ${dashboard.metricsSnapshot.summary.totalMetrics}`);
  console.log(`   Active Alerts: ${dashboard.activeAlerts.length}`);
  console.log(`   Avg Response Time: ${dashboard.systemStats.avgResponseTime.toFixed(1)}ms`);
  console.log(`   Error Rate: ${dashboard.systemStats.errorRate.toFixed(2)}%`);

  if (dashboard.healthStatus.issues.length > 0) {
    console.log(`   Issues: ${dashboard.healthStatus.issues.join(', ')}`);
  }
}

function showActiveAlerts(system: MonitoringSystem): void {
  const alerts = system.getActiveAlerts();
  
  if (alerts.length === 0) {
    console.log('   ✅ No active alerts');
    return;
  }

  alerts.forEach((alert: any, index: number) => {
    const icon = alert.severity === 'critical' ? '🚨' : 
                 alert.severity === 'warning' ? '⚠️' : 'ℹ️';
    const duration = formatDuration(alert.duration);
    console.log(`   ${icon} [${alert.severity.toUpperCase()}] ${alert.message} (${duration})`);
  });
}

function showSystemHealth(system: MonitoringSystem): void {
  const health = system.getHealthStatus();
  const dashboard = system.getDashboard();
  
  console.log('┌─────────────────────────────────────┐');
  console.log('│          System Health              │');
  console.log('├─────────────────────────────────────┤');
  console.log(`│ Status: ${getHealthIcon(health.overall)} ${health.overall.padEnd(18)} │`);
  console.log(`│ Uptime: ${formatDuration(health.metrics.uptime).padEnd(22)} │`);
  console.log(`│ Metrics: ${health.metrics.metricsCount.toString().padEnd(21)} │`);
  console.log(`│ Alerts: ${health.metrics.activeAlerts.toString().padEnd(22)} │`);
  console.log('├─────────────────────────────────────┤');
  console.log('│           Components                │');
  console.log('├─────────────────────────────────────┤');
  console.log(`│ Monitor: ${getComponentIcon(health.components.performanceMonitor).padEnd(23)} │`);
  console.log(`│ Metrics: ${getComponentIcon(health.components.metricsCollector).padEnd(23)} │`);
  console.log(`│ Alerts:  ${getComponentIcon(health.components.alertManager).padEnd(23)} │`);
  console.log('└─────────────────────────────────────┘');

  const summary = system.getAlertSummary();
  if (summary.total > 0) {
    console.log('\n📊 Alert Summary:');
    console.log(`   Critical: ${summary.bySeverity.critical}`);
    console.log(`   Warning:  ${summary.bySeverity.warning}`);
    console.log(`   Info:     ${summary.bySeverity.info}`);
  }
}

function exportMetrics(system: MonitoringSystem): void {
  try {
    const jsonExport = system.exportMetrics('json');
    const metricsData = JSON.parse(jsonExport);
    
    console.log(`   ✓ JSON export: ${metricsData.summary.totalMetrics} metrics`);
    console.log(`   ✓ Time range: ${metricsData.summary.timeRange.start} - ${metricsData.summary.timeRange.end}`);
    
    const prometheusExport = system.exportMetrics('prometheus');
    const prometheusLines = prometheusExport.split('\n').filter(line => 
      line && !line.startsWith('#')
    ).length;
    
    console.log(`   ✓ Prometheus export: ${prometheusLines} metric lines`);
    
  } catch (error) {
    console.log(`   ❌ Export error: ${error}`);
  }
}

// Utility functions
function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function formatDuration(ms: number): string {
  const seconds = Math.floor(ms / 1000);
  const minutes = Math.floor(seconds / 60);
  const hours = Math.floor(minutes / 60);
  
  if (hours > 0) {
    return `${hours}h ${minutes % 60}m ${seconds % 60}s`;
  } else if (minutes > 0) {
    return `${minutes}m ${seconds % 60}s`;
  } else {
    return `${seconds}s`;
  }
}

function getHealthIcon(health: string): string {
  switch (health) {
    case 'healthy': return '💚';
    case 'degraded': return '💛';
    case 'critical': return '💔';
    default: return '❓';
  }
}

function getComponentIcon(status: string): string {
  switch (status) {
    case 'running': return '🟢 Running';
    case 'stopped': return '🔴 Stopped';
    case 'error': return '❌ Error';
    default: return '❓ Unknown';
  }
}

// Run the demo
if (import.meta.url === `file://${process.argv[1]}`) {
  runMonitoringDemo().catch(console.error);
}

export { runMonitoringDemo };