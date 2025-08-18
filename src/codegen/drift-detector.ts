/**
 * Drift Detection System
 * Monitors changes in generated code and specifications
 */

import { createHash } from 'crypto';
import { readFileSync, writeFileSync, existsSync } from 'fs';
import { join, dirname } from 'path';
import { glob } from 'glob';
import chalk from 'chalk';
import { CodegenManifest, DriftDetectionResult } from './deterministic-generator.js';

export interface DriftConfig {
  /** Directory containing generated code */
  codeDir: string;
  /** Path to AE-IR specification file */
  specPath: string;
  /** Path to codegen manifest */
  manifestPath?: string;
  /** Files to ignore during drift detection */
  ignorePatterns?: string[];
  /** Enable detailed reporting */
  verbose?: boolean;
  /** Auto-fix simple drift issues */
  autoFix?: boolean;
}

export interface FileChangeInfo {
  /** File path relative to codeDir */
  filePath: string;
  /** Change type */
  changeType: 'modified' | 'added' | 'deleted' | 'renamed';
  /** Previous hash (for modified files) */
  previousHash?: string;
  /** Current hash */
  currentHash?: string;
  /** Change timestamp */
  detectedAt: string;
  /** Lines changed (approximate) */
  linesChanged?: number;
  /** Confidence level of detection */
  confidence: 'high' | 'medium' | 'low';
}

export interface DriftReport {
  /** Overall drift status */
  status: 'no_drift' | 'minor_drift' | 'major_drift' | 'critical_drift';
  /** Summary statistics */
  summary: {
    totalFiles: number;
    changedFiles: number;
    addedFiles: number;
    deletedFiles: number;
    unchangedFiles: number;
  };
  /** Detailed change information */
  changes: FileChangeInfo[];
  /** Specification change detection */
  specificationChange: {
    hasChanged: boolean;
    previousHash?: string;
    currentHash?: string;
    changesSince?: string;
  };
  /** Recommendations */
  recommendations: string[];
  /** Generated at timestamp */
  generatedAt: string;
}

// Configuration constants for drift detection
const DEFAULT_LINE_CHANGE_ESTIMATE_RATIO = 0.1; // 10% estimated change ratio
const FALLBACK_ORIGINAL_LINES = 100; // Fallback when original line count unknown

export class DriftDetector {
  private config: DriftConfig;

  constructor(config: DriftConfig) {
    this.config = {
      manifestPath: join(config.codeDir, '.codegen-manifest.json'),
      ignorePatterns: [
        '**/.git/**',
        '**/node_modules/**',
        '**/.codegen-manifest.json',
        '**/dist/**',
        '**/build/**',
      ],
      verbose: false,
      autoFix: false,
      ...config,
    };
  }

  /**
   * Perform comprehensive drift detection
   */
  async detectDrift(): Promise<DriftReport> {
    const startTime = Date.now();
    
    if (this.config.verbose) {
      console.log(chalk.blue('🔍 Starting drift detection...'));
    }

    // Load previous state
    const manifest = this.loadManifest();
    const changes: FileChangeInfo[] = [];

    // Detect specification changes
    const specChange = await this.detectSpecificationChanges(manifest);
    
    // Scan for file changes
    const fileChanges = await this.scanFileChanges(manifest);
    changes.push(...fileChanges);

    // Detect new/deleted files
    const structuralChanges = await this.detectStructuralChanges(manifest);
    changes.push(...structuralChanges);

    // Generate summary
    const summary = this.generateSummary(changes);
    const status = this.calculateDriftStatus(changes, specChange);
    const recommendations = this.generateRecommendations(changes, specChange, status);

    const report: DriftReport = {
      status,
      summary,
      changes,
      specificationChange: specChange,
      recommendations,
      generatedAt: new Date().toISOString(),
    };

    // Auto-fix if enabled
    if (this.config.autoFix && status === 'minor_drift') {
      await this.autoFixMinorIssues(changes);
    }

    if (this.config.verbose) {
      console.log(chalk.green(`✅ Drift detection completed in ${Date.now() - startTime}ms`));
      this.printReport(report);
    }

    return report;
  }

  /**
   * Detect changes in the specification file
   */
  private async detectSpecificationChanges(manifest?: CodegenManifest): Promise<DriftReport['specificationChange']> {
    if (!existsSync(this.config.specPath)) {
      return {
        hasChanged: true, // Missing spec is a critical change
      };
    }

    const currentContent = readFileSync(this.config.specPath, 'utf-8');
    const currentHash = this.calculateHash(currentContent);

    if (!manifest) {
      return {
        hasChanged: false,
        currentHash,
      };
    }

    return {
      hasChanged: manifest.metadata.specHash !== currentHash,
      previousHash: manifest.metadata.specHash,
      currentHash,
      changesSince: manifest.metadata.generatedAt,
    };
  }

  /**
   * Scan for changes in existing files
   */
  private async scanFileChanges(manifest?: CodegenManifest): Promise<FileChangeInfo[]> {
    if (!manifest) return [];

    const changes: FileChangeInfo[] = [];

    for (const file of manifest.files) {
      const fullPath = join(this.config.codeDir, file.filePath);
      
      if (!existsSync(fullPath)) {
        changes.push({
          filePath: file.filePath,
          changeType: 'deleted',
          previousHash: file.hash,
          detectedAt: new Date().toISOString(),
          confidence: 'high',
        });
        continue;
      }

      const currentContent = readFileSync(fullPath, 'utf-8');
      const currentHash = this.calculateHash(currentContent);

      if (currentHash !== file.hash) {
        const linesChanged = this.estimateLinesChanged(currentContent, file.hash);
        
        changes.push({
          filePath: file.filePath,
          changeType: 'modified',
          previousHash: file.hash,
          currentHash,
          detectedAt: new Date().toISOString(),
          linesChanged,
          confidence: this.calculateChangeConfidence(currentContent, file),
        });
      }
    }

    return changes;
  }

  /**
   * Detect new files and structural changes
   */
  private async detectStructuralChanges(manifest?: CodegenManifest): Promise<FileChangeInfo[]> {
    const changes: FileChangeInfo[] = [];
    const knownFiles = new Set(manifest?.files.map(f => f.filePath) || []);

    // Find all files in the code directory
    const allFiles = await glob('**/*', {
      cwd: this.config.codeDir,
      ignore: this.config.ignorePatterns,
      nodir: true,
    });

    for (const filePath of allFiles) {
      if (!knownFiles.has(filePath)) {
        const fullPath = join(this.config.codeDir, filePath);
        const content = readFileSync(fullPath, 'utf-8');
        const currentHash = this.calculateHash(content);

        // Check if this looks like a generated file
        const isGenerated = this.isLikelyGeneratedFile(content, filePath);

        changes.push({
          filePath,
          changeType: 'added',
          currentHash,
          detectedAt: new Date().toISOString(),
          confidence: isGenerated ? 'high' : 'low',
        });
      }
    }

    return changes;
  }

  /**
   * Calculate drift severity status
   */
  private calculateDriftStatus(changes: FileChangeInfo[], specChange: DriftReport['specificationChange']): DriftReport['status'] {
    // Critical: Specification changed
    if (specChange.hasChanged) {
      return 'critical_drift';
    }

    const highConfidenceChanges = changes.filter(c => c.confidence === 'high');
    const deletedFiles = changes.filter(c => c.changeType === 'deleted');
    const modifiedFiles = changes.filter(c => c.changeType === 'modified');

    // Critical: Many deleted files
    if (deletedFiles.length > 3) {
      return 'critical_drift';
    }

    // Major: Many high-confidence changes
    if (highConfidenceChanges.length > 5) {
      return 'major_drift';
    }

    // Minor: Some modifications
    if (modifiedFiles.length > 0 || changes.length > 0) {
      return 'minor_drift';
    }

    return 'no_drift';
  }

  /**
   * Generate actionable recommendations
   */
  private generateRecommendations(
    changes: FileChangeInfo[],
    specChange: DriftReport['specificationChange'],
    status: DriftReport['status']
  ): string[] {
    const recommendations: string[] = [];

    if (specChange.hasChanged) {
      recommendations.push('🔄 Specification has changed - regenerate all code to ensure consistency');
      recommendations.push('📝 Review specification changes before regenerating');
    }

    const modifiedFiles = changes.filter(c => c.changeType === 'modified');
    if (modifiedFiles.length > 0) {
      recommendations.push(`📁 ${modifiedFiles.length} files have manual modifications`);
      recommendations.push('🔍 Review changes before regenerating to preserve important modifications');
    }

    const deletedFiles = changes.filter(c => c.changeType === 'deleted');
    if (deletedFiles.length > 0) {
      recommendations.push(`❌ ${deletedFiles.length} generated files are missing`);
      recommendations.push('🔄 Regenerate code to restore missing files');
    }

    const addedFiles = changes.filter(c => c.changeType === 'added');
    if (addedFiles.length > 0) {
      recommendations.push(`➕ ${addedFiles.length} new files detected`);
      recommendations.push('🧹 Consider adding to .gitignore if these are build artifacts');
    }

    switch (status) {
      case 'critical_drift':
        recommendations.push('🚨 Critical drift detected - immediate action required');
        recommendations.push('⏱️  Run regeneration as soon as possible');
        break;
      case 'major_drift':
        recommendations.push('⚠️  Major drift detected - plan regeneration soon');
        break;
      case 'minor_drift':
        recommendations.push('ℹ️  Minor drift detected - regeneration recommended');
        break;
    }

    return recommendations;
  }

  /**
   * Auto-fix minor drift issues
   */
  private async autoFixMinorIssues(changes: FileChangeInfo[]): Promise<void> {
    if (this.config.verbose) {
      console.log(chalk.yellow('🔧 Auto-fixing minor drift issues...'));
    }

    // For now, just log what would be fixed
    // In practice, this could restore deleted generated files, 
    // update timestamps, etc.
    for (const change of changes) {
      if (change.changeType === 'deleted' && change.confidence === 'high') {
        console.log(chalk.yellow(`  Would restore: ${change.filePath}`));
      }
    }
  }

  /**
   * Helper methods
   */
  private loadManifest(): CodegenManifest | undefined {
    if (!this.config.manifestPath || !existsSync(this.config.manifestPath)) {
      return undefined;
    }

    try {
      const content = readFileSync(this.config.manifestPath, 'utf-8');
      return JSON.parse(content);
    } catch (error) {
      if (this.config.verbose) {
        console.warn(chalk.yellow('⚠️  Could not load manifest file'));
      }
      return undefined;
    }
  }

  private calculateHash(content: string): string {
    return createHash('sha256').update(content).digest('hex');
  }

  private estimateLinesChanged(content: string, expectedHash: string): number {
    // Simplified line change estimation
    // In practice, this could use diff algorithms
    const lines = content.split('\n').length;
    return Math.floor(lines * DEFAULT_LINE_CHANGE_ESTIMATE_RATIO);
  }

  private calculateChangeConfidence(content: string, originalFile: any): 'high' | 'medium' | 'low' {
    // Check for generated file markers
    if (content.includes('DO NOT MODIFY') || content.includes('automatically generated')) {
      return 'high';
    }

    // Check for significant structural changes
    const currentLines = content.split('\n').length;
    const estimatedOriginalLines = this.getOriginalLineCount(originalFile);
    if (estimatedOriginalLines === undefined || estimatedOriginalLines === 0) {
      if (this.config.verbose) {
        console.warn(chalk.yellow('⚠️  Could not determine original line count, using fallback of 100'));
      }
    }
    const baseLines = (estimatedOriginalLines && estimatedOriginalLines > 0) ? estimatedOriginalLines : FALLBACK_ORIGINAL_LINES;
    const changeRatio = Math.abs(currentLines - baseLines) / baseLines;

    if (changeRatio > 0.5) return 'high';
    if (changeRatio > 0.2) return 'medium';
    return 'low';
  }

  /**
   * Attempts to determine the original line count from the manifest or original file content.
   */
  private getOriginalLineCount(originalFile: any): number | undefined {
    // If originalFile is a string (content), count lines
    if (typeof originalFile === 'string') {
      return originalFile.split('\n').length;
    }
    // If originalFile is an object with a 'content' property
    if (originalFile && typeof originalFile.content === 'string') {
      return originalFile.content.split('\n').length;
    }
    // If originalFile is an object with a 'lines' property
    if (originalFile && typeof originalFile.lines === 'number') {
      return originalFile.lines;
    }
    // Could not determine
    return undefined;
  }
  private isLikelyGeneratedFile(content: string, filePath: string): boolean {
    // Check for generated file indicators
    const generatedMarkers = [
      'DO NOT MODIFY',
      'automatically generated',
      'Generated from AE-IR',
      'codegen',
    ];

    return generatedMarkers.some(marker => content.includes(marker)) ||
           filePath.includes('.generated.') ||
           filePath.startsWith('generated/');
  }

  private generateSummary(changes: FileChangeInfo[]): DriftReport['summary'] {
    return {
      totalFiles: changes.length,
      changedFiles: changes.filter(c => c.changeType === 'modified').length,
      addedFiles: changes.filter(c => c.changeType === 'added').length,
      deletedFiles: changes.filter(c => c.changeType === 'deleted').length,
      unchangedFiles: 0, // Would need to calculate from manifest
    };
  }

  private printReport(report: DriftReport): void {
    console.log(chalk.blue('\n📊 Drift Detection Report'));
    console.log(chalk.blue('========================'));
    
    // Status
    const statusColors = {
      'no_drift': chalk.green,
      'minor_drift': chalk.yellow,
      'major_drift': chalk.red,
      'critical_drift': chalk.red.bold,
    };
    console.log(`Status: ${statusColors[report.status](report.status.toUpperCase())}`);

    // Summary
    console.log('\n📈 Summary:');
    console.log(`  Total files: ${report.summary.totalFiles}`);
    console.log(`  Modified: ${report.summary.changedFiles}`);
    console.log(`  Added: ${report.summary.addedFiles}`);
    console.log(`  Deleted: ${report.summary.deletedFiles}`);

    // Specification changes
    if (report.specificationChange.hasChanged) {
      console.log(chalk.red('\n🔄 Specification Changes Detected'));
    }

    // Recommendations
    if (report.recommendations.length > 0) {
      console.log('\n💡 Recommendations:');
      report.recommendations.forEach(rec => console.log(`  ${rec}`));
    }

    console.log('');
  }
}