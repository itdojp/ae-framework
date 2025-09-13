import { writeFileSync, readFileSync, existsSync, mkdirSync } from 'fs';
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
      sessionId: this.generateSessionId()
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

  private saveMetrics(): void {
    const metricsFile = path.join(this.metricsPath, 'project-metrics.json');
    writeFileSync(metricsFile, JSON.stringify(this.projectMetrics, null, 2));
  }

  private saveViolationLog(violation: TDDViolation): void {
    const logFile = path.join(this.metricsPath, 'violations.log');
    const logEntry = `${violation.timestamp.toISOString()} [${violation.severity.toUpperCase()}] ${violation.type}: ${violation.message} (Phase: ${violation.phase})\n`;
    
    try {
      if (existsSync(logFile)) {
        const currentLog = readFileSync(logFile, 'utf8');
        writeFileSync(logFile, currentLog + logEntry);
      } else {
        writeFileSync(logFile, logEntry);
      }
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
    const report = {
      summary: {
        project: this.projectMetrics.projectName,
        session: this.projectMetrics.sessionId,
        duration: Date.now() - this.projectMetrics.startTime.getTime(),
        phases_completed: this.projectMetrics.phases.filter(p => p.endTime).length,
        total_phases: this.projectMetrics.phases.length,
        tdd_compliance: `${this.projectMetrics.tddCompliance.toFixed(1)}%`,
        overall_coverage: `${this.projectMetrics.overallCoverage.toFixed(1)}%`,
        total_violations: this.projectMetrics.totalViolations
      },
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
