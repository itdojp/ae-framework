import { writeFileSync, appendFileSync, mkdirSync, existsSync, readFileSync } from 'fs';
import * as path from 'path';
import type { AEFrameworkConfig } from '../types.js';
import { toMessage } from '../../utils/error-utils.js';

export interface TDDViolation {
  timestamp: Date;
  type: 'code_without_test' | 'test_not_run' | 'skip_red_phase' | 'coverage_low';
  file?: string;
  phase: string;
  message: string;
  severity: 'error' | 'warning';
}

export interface PhaseMetrics {
  phase: string;
  startTime: Date;
  endTime?: Date;
  duration?: number; // milliseconds
  artifacts_created: string[];
  tests_written: number;
  tests_passed: number;
  coverage: number;
  violations: TDDViolation[];
}

export interface ProjectMetrics {
  projectName: string;
  startTime: Date;
  phases: PhaseMetrics[];
  totalViolations: number;
  tddCompliance: number; // percentage
  overallCoverage: number;
  sessionId: string;
  incidents: MTTRIncident[];
}

export interface MTTRIncident {
  id: string;
  detectedAt: Date;
  recoveredAt?: Date;
  durationMs?: number;
  source?: string;
  message?: string;
  severity?: 'error' | 'warning';
}

export interface MTTRSummary {
  overallMs: number | null;
  overallHours: number | null;
  weekly: Array<{
    week: string;
    count: number;
    avgMs: number;
    avgHours: number;
  }>;
  openIncidents: number;
}

export interface Logger {
  warn(message: string): void;
  info(message: string): void;
  error(message: string): void;
}

export class MetricsCollector {
  private projectMetrics: ProjectMetrics;
  private metricsPath: string;
  private logger: Logger;

  constructor(private _config: AEFrameworkConfig, logger?: Logger) {
    this.logger = logger || {
      warn: (msg: string) => console.warn(msg),
      info: (msg: string) => console.log(msg),
      error: (msg: string) => console.error(msg)
    };
    this.metricsPath = path.join(process.cwd(), _config.metrics.export.path);
    this.ensureMetricsDirectory();
    this.projectMetrics = this.loadOrCreateProjectMetrics();
  }

  private ensureMetricsDirectory(): void {
    if (!existsSync(this.metricsPath)) {
      mkdirSync(this.metricsPath, { recursive: true });
    }
  }

  private loadOrCreateProjectMetrics(): ProjectMetrics {
    const metricsFile = path.join(this.metricsPath, 'project-metrics.json');
    
    if (existsSync(metricsFile)) {
      try {
        const data = readFileSync(metricsFile, 'utf8');
        const metrics = JSON.parse(data);
        // Convert date strings back to Date objects
        metrics.startTime = new Date(metrics.startTime);
        metrics.phases.forEach((phase: any) => {
          phase.startTime = new Date(phase.startTime);
          if (phase.endTime) phase.endTime = new Date(phase.endTime);
          phase.violations.forEach((violation: any) => {
            violation.timestamp = new Date(violation.timestamp);
          });
        });
        if (!Array.isArray(metrics.incidents)) {
          metrics.incidents = [];
        }
        metrics.incidents.forEach((incident: any) => {
          incident.detectedAt = new Date(incident.detectedAt);
          if (incident.recoveredAt) incident.recoveredAt = new Date(incident.recoveredAt);
        });
        return metrics;
      } catch (error: unknown) {
        console.warn(`Could not load existing metrics: ${toMessage(error)}`);
      }
    }

    return {
      projectName: path.basename(process.cwd()),
      startTime: new Date(),
      phases: [],
      totalViolations: 0,
      tddCompliance: 100,
      overallCoverage: 0,
      sessionId: this.generateSessionId(),
      incidents: [],
    };
  }

  startPhase(phaseName: string): void {
    // End previous phase if exists
    const currentPhase = this.getCurrentPhase();
    if (currentPhase && !currentPhase.endTime) {
      this.endPhase();
    }

    const phaseMetrics: PhaseMetrics = {
      phase: phaseName,
      startTime: new Date(),
      artifacts_created: [],
      tests_written: 0,
      tests_passed: 0,
      coverage: 0,
      violations: []
    };

    this.projectMetrics.phases.push(phaseMetrics);
    this.saveMetrics();
  }

  endPhase(): void {
    const currentPhase = this.getCurrentPhase();
    if (currentPhase && !currentPhase.endTime) {
      currentPhase.endTime = new Date();
      currentPhase.duration = currentPhase.endTime.getTime() - currentPhase.startTime.getTime();
      this.resolveIncidentsForPhase(currentPhase);
      this.saveMetrics();
    }
  }

  recordViolation(violation: Omit<TDDViolation, 'timestamp'>): void {
    const fullViolation: TDDViolation = {
      ...violation,
      timestamp: new Date()
    };

    // Add to current phase
    const currentPhase = this.getCurrentPhase();
    if (currentPhase) {
      currentPhase.violations.push(fullViolation);
    }

    // Update project totals
    this.projectMetrics.totalViolations++;
    this.updateTDDCompliance();
    this.saveMetrics();

    // Log violation for immediate visibility
    this.logger.warn(`🚨 TDD Violation: ${violation.message}`);
    
    // Save detailed violation log
    this.saveViolationLog(fullViolation);

    if (violation.severity === 'error') {
      this.recordFailureDetected({
        source: `tdd_violation:${violation.type}`,
        message: violation.message,
        severity: violation.severity,
      });
    }
  }

  recordArtifact(artifactPath: string): void {
    const currentPhase = this.getCurrentPhase();
    if (currentPhase) {
      currentPhase.artifacts_created.push(artifactPath);
      this.saveMetrics();
    }
  }

  recordTestMetrics(testsWritten: number, testsPassed: number, coverage: number): void {
    const currentPhase = this.getCurrentPhase();
    if (currentPhase) {
      currentPhase.tests_written = testsWritten;
      currentPhase.tests_passed = testsPassed;
      currentPhase.coverage = coverage;
      
      // Update overall coverage
      this.updateOverallCoverage();
      this.saveMetrics();
    }
  }

  recordFailureDetected(details: { source?: string; message?: string; severity?: 'error' | 'warning' }): string {
    const source = details.source;
    if (source && this.projectMetrics.incidents.some((incident) => !incident.recoveredAt && incident.source === source)) {
      return this.projectMetrics.incidents.find((incident) => !incident.recoveredAt && incident.source === source)?.id ?? '';
    }

    const incident: MTTRIncident = {
      id: this.generateSessionId(),
      detectedAt: new Date(),
      source,
      message: details.message,
      severity: details.severity,
    };

    this.projectMetrics.incidents.push(incident);
    this.saveMetrics();
    return incident.id;
  }

  recordFailureRecovered(incidentId: string): boolean {
    const incident = this.projectMetrics.incidents.find((entry) => entry.id === incidentId);
    if (!incident || incident.recoveredAt) {
      return false;
    }
    incident.recoveredAt = new Date();
    incident.durationMs = incident.recoveredAt.getTime() - incident.detectedAt.getTime();
    this.saveMetrics();
    return true;
  }

  resolveOpenIncidents(reason?: string): number {
    const now = new Date();
    let resolved = 0;
    this.projectMetrics.incidents.forEach((incident) => {
      if (incident.recoveredAt) return;
      incident.recoveredAt = now;
      incident.durationMs = incident.recoveredAt.getTime() - incident.detectedAt.getTime();
      if (reason && !incident.message) {
        incident.message = reason;
      }
      resolved += 1;
    });
    if (resolved > 0) {
      this.saveMetrics();
    }
    return resolved;
  }

  private getCurrentPhase(): PhaseMetrics | undefined {
    return this.projectMetrics.phases[this.projectMetrics.phases.length - 1];
  }

  private updateTDDCompliance(): void {
    const totalActions = this.projectMetrics.phases.reduce(
      (sum, phase) => sum + phase.artifacts_created.length + phase.tests_written, 
      0
    );
    
    if (totalActions > 0) {
      this.projectMetrics.tddCompliance = Math.max(
        0, 
        100 - (this.projectMetrics.totalViolations / totalActions) * 100
      );
    }
  }

  private updateOverallCoverage(): void {
    const phases = this.projectMetrics.phases.filter(p => p.coverage > 0);
    if (phases.length > 0) {
      this.projectMetrics.overallCoverage = 
        phases.reduce((sum, p) => sum + p.coverage, 0) / phases.length;
    }
  }

  private resolveIncidentsForPhase(phase: PhaseMetrics): void {
    if (!phase.endTime || phase.violations.length === 0) return;
    const sources = new Set(phase.violations.map((v) => `tdd_violation:${v.type}`));
    const endTime = phase.endTime;
    this.projectMetrics.incidents.forEach((incident) => {
      if (incident.recoveredAt) return;
      if (!incident.source || !sources.has(incident.source)) return;
      incident.recoveredAt = endTime;
      incident.durationMs = incident.recoveredAt.getTime() - incident.detectedAt.getTime();
    });
  }

  private saveMetrics(): void {
    const metricsFile = path.join(this.metricsPath, 'project-metrics.json');
    writeFileSync(metricsFile, JSON.stringify(this.projectMetrics, null, 2));
  }

  private saveViolationLog(violation: TDDViolation): void {
    const logFile = path.join(this.metricsPath, 'violations.log');
    const logEntry = `${violation.timestamp.toISOString()} [${violation.severity.toUpperCase()}] ${violation.type}: ${violation.message} (Phase: ${violation.phase})\n`;
    
    try {
      appendFileSync(logFile, logEntry);
    } catch (error: unknown) {
      console.warn(`Could not save violation log: ${toMessage(error)}`);
    }
  }

  private generateSessionId(): string {
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const random = Math.random().toString(36).substring(2, 8);
    return `${timestamp}-${random}`;
  }

  generateReport(): string {
    const mttr = this.computeMTTRSummary();
    const report = {
      summary: {
        project: this.projectMetrics.projectName,
        session: this.projectMetrics.sessionId,
        duration: Date.now() - this.projectMetrics.startTime.getTime(),
        phases_completed: this.projectMetrics.phases.filter(p => p.endTime).length,
        total_phases: this.projectMetrics.phases.length,
        tdd_compliance: `${this.projectMetrics.tddCompliance.toFixed(1)}%`,
        overall_coverage: `${this.projectMetrics.overallCoverage.toFixed(1)}%`,
        total_violations: this.projectMetrics.totalViolations,
        mttr_hours: mttr.overallHours ?? 'n/a',
        mttr_open_incidents: mttr.openIncidents,
      },
      mttr,
      phases: this.projectMetrics.phases.map(phase => ({
        name: phase.phase,
        duration: phase.duration ? `${(phase.duration / 1000).toFixed(1)}s` : 'In progress',
        artifacts: phase.artifacts_created.length,
        tests: `${phase.tests_passed}/${phase.tests_written}`,
        coverage: `${phase.coverage.toFixed(1)}%`,
        violations: phase.violations.length
      })),
      top_violations: this.getTopViolations(),
      recommendations: this.generateRecommendations()
    };

    return JSON.stringify(report, null, 2);
  }

  private computeMTTRSummary(): MTTRSummary {
    const completed = this.projectMetrics.incidents.filter((incident) => incident.recoveredAt && incident.durationMs !== undefined);
    const openIncidents = this.projectMetrics.incidents.filter((incident) => !incident.recoveredAt).length;
    if (completed.length === 0) {
      return { overallMs: null, overallHours: null, weekly: [], openIncidents };
    }

    const overallMs = completed.reduce((sum, incident) => sum + (incident.durationMs ?? 0), 0) / completed.length;
    const overallHours = Number((overallMs / (1000 * 60 * 60)).toFixed(2));

    const weeklyMap = new Map<string, number[]>();
    completed.forEach((incident) => {
      const recoveredAt = incident.recoveredAt ?? incident.detectedAt;
      const week = this.toIsoWeek(recoveredAt);
      if (!weeklyMap.has(week)) weeklyMap.set(week, []);
      weeklyMap.get(week)?.push(incident.durationMs ?? 0);
    });

    const weekly = Array.from(weeklyMap.entries())
      .map(([week, durations]) => {
        const avgMs = durations.reduce((sum, value) => sum + value, 0) / durations.length;
        return {
          week,
          count: durations.length,
          avgMs,
          avgHours: Number((avgMs / (1000 * 60 * 60)).toFixed(2)),
        };
      })
      .sort((a, b) => a.week.localeCompare(b.week));

    return {
      overallMs,
      overallHours,
      weekly,
      openIncidents,
    };
  }

  private toIsoWeek(date: Date): string {
    const temp = new Date(Date.UTC(date.getUTCFullYear(), date.getUTCMonth(), date.getUTCDate()));
    const dayNum = temp.getUTCDay() || 7;
    temp.setUTCDate(temp.getUTCDate() + 4 - dayNum);
    const yearStart = new Date(Date.UTC(temp.getUTCFullYear(), 0, 1));
    const weekNo = Math.ceil((((temp.getTime() - yearStart.getTime()) / 86400000) + 1) / 7);
    return `${temp.getUTCFullYear()}-W${String(weekNo).padStart(2, '0')}`;
  }

  private getTopViolations(): Array<{type: string, count: number}> {
    const violationCounts: Record<string, number> = {};
    
    this.projectMetrics.phases.forEach(phase => {
      phase.violations.forEach(violation => {
        violationCounts[violation.type] = (violationCounts[violation.type] || 0) + 1;
      });
    });

    return Object.entries(violationCounts)
      .map(([type, count]) => ({ type, count }))
      .sort((a, b) => b.count - a.count)
      .slice(0, 5);
  }

  private generateRecommendations(): string[] {
    const recommendations: string[] = [];
    
    if (this.projectMetrics.tddCompliance < 80) {
      recommendations.push("Consider using stricter TDD enforcement settings");
    }
    
    if (this.projectMetrics.overallCoverage < 80) {
      recommendations.push("Increase test coverage to meet the 80% threshold");
    }
    
    const codeWithoutTestViolations = this.projectMetrics.phases
      .flatMap(p => p.violations)
      .filter(v => v.type === 'code_without_test').length;
      
    if (codeWithoutTestViolations > 0) {
      recommendations.push("Focus on writing tests before implementation");
    }

    if (recommendations.length === 0) {
      recommendations.push("Excellent TDD compliance! Keep up the good work!");
    }

    return recommendations;
  }
}
