#!/usr/bin/env node

/**
 * Project Cleanup and Organization Script
 * Cleans up temporary files, organizes reports, and maintains project structure
 */

import fs from 'fs';
import path from 'path';
import { glob } from 'glob';

class ProjectCleaner {
  constructor() {
    this.rootDir = process.cwd();
    this.cleanupStats = {
      filesRemoved: 0,
      filesArchived: 0,
      directoriesCreated: 0,
      spaceSaved: 0
    };
  }

  async analyzeProjectStructure() {
    console.log('🔍 Analyzing project structure...');
    
    const analysis = {
      temporaryFiles: [],
      reportFiles: [],
      largeFiles: [],
      emptyDirectories: []
    };

    // Find temporary report files
    const cegisReports = await glob('cegis-report-*.json', { cwd: this.rootDir });
    const sampleFiles = await glob('sample-*.json', { cwd: this.rootDir });
    const invalidFiles = await glob('invalid-sample-*.json', { cwd: this.rootDir });
    
    analysis.temporaryFiles = [...cegisReports, ...sampleFiles, ...invalidFiles];
    
    // Find report files in reports directory
    if (fs.existsSync('reports')) {
      const reportFiles = await glob('reports/**/*.{json,xml,txt,html}', { cwd: this.rootDir });
      analysis.reportFiles = reportFiles;
    }

    // Find large files (>10MB)
    const allFiles = await glob('**/*', { 
      cwd: this.rootDir, 
      ignore: ['node_modules/**', 'dist/**', '.git/**'],
      nodir: true
    });
    
    for (const file of allFiles) {
      try {
        const stats = fs.statSync(file);
        if (stats.size > 10 * 1024 * 1024) { // 10MB
          analysis.largeFiles.push({
            path: file,
            size: stats.size,
            sizeHuman: this.formatBytes(stats.size)
          });
        }
      } catch (error) {
        // Skip files that can't be accessed
      }
    }

    return analysis;
  }

  async createArchiveStructure() {
    console.log('📁 Creating archive structure...');
    
    const archiveDirs = [
      'temp-reports/cegis-archives',
      'temp-reports/sample-data-archives',
      'temp-reports/conformance-archives',
      'temp-reports/build-artifacts'
    ];

    for (const dir of archiveDirs) {
      if (!fs.existsSync(dir)) {
        fs.mkdirSync(dir, { recursive: true });
        this.cleanupStats.directoriesCreated++;
        console.log(`   ✅ Created: ${dir}`);
      }
    }
  }

  async archiveTemporaryFiles(analysis) {
    console.log('📦 Archiving temporary files...');
    
    const archiveMap = {
      'cegis-report-*.json': 'temp-reports/cegis-archives/',
      'sample-*.json': 'temp-reports/sample-data-archives/',
      'invalid-sample-*.json': 'temp-reports/sample-data-archives/',
      'clean-sample-*.json': 'temp-reports/sample-data-archives/',
      'conformance-results.json': 'temp-reports/conformance-archives/'
    };

    for (const [pattern, targetDir] of Object.entries(archiveMap)) {
      const files = await glob(pattern, { cwd: this.rootDir });
      
      for (const file of files) {
        try {
          const stats = fs.statSync(file);
          const targetPath = path.join(targetDir, path.basename(file));
          
          // Add timestamp to avoid conflicts
          const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
          const finalPath = targetPath.replace('.json', `_${timestamp}.json`);
          
          fs.renameSync(file, finalPath);
          this.cleanupStats.filesArchived++;
          this.cleanupStats.spaceSaved += stats.size;
          
          console.log(`   📦 Archived: ${file} → ${finalPath}`);
        } catch (error) {
          console.warn(`   ⚠️  Failed to archive ${file}: ${error.message}`);
        }
      }
    }
  }

  async cleanupBuildArtifacts() {
    console.log('🧹 Cleaning build artifacts...');
    
    const buildPatterns = [
      '.nyc_output/**/*',
      '.stryker-tmp/**/*',
      'coverage/**/*',
      'dist/**/*.map',
      'test_timing.log',
      'mutation-report/**/*'
    ];

    for (const pattern of buildPatterns) {
      try {
        const files = await glob(pattern, { cwd: this.rootDir });
        
        for (const file of files) {
          try {
            const stats = fs.statSync(file);
            if (stats.isFile()) {
              fs.unlinkSync(file);
              this.cleanupStats.filesRemoved++;
              this.cleanupStats.spaceSaved += stats.size;
              console.log(`   🗑️  Removed: ${file}`);
            }
          } catch (error) {
            // Skip files that can't be removed
          }
        }
      } catch (error) {
        // Skip patterns that don't match anything
      }
    }
  }

  async optimizeReportsDirectory() {
    console.log('📊 Optimizing reports directory...');
    
    if (!fs.existsSync('reports')) {
      console.log('   ℹ️  No reports directory found');
      return;
    }

    // Group reports by type and date
    const reportsDir = 'reports';
    const files = fs.readdirSync(reportsDir, { recursive: true });
    const reportTypes = new Map();

    for (const file of files) {
      const filePath = path.join(reportsDir, file);
      
      if (fs.statSync(filePath).isFile()) {
        const ext = path.extname(file);
        const type = this.categorizeReport(file);
        
        if (!reportTypes.has(type)) {
          reportTypes.set(type, []);
        }
        
        reportTypes.get(type).push({
          path: filePath,
          name: file,
          size: fs.statSync(filePath).size,
          mtime: fs.statSync(filePath).mtime
        });
      }
    }

    // Create organized structure
    for (const [type, files] of reportTypes) {
      const typeDir = path.join(reportsDir, type);
      if (!fs.existsSync(typeDir)) {
        fs.mkdirSync(typeDir, { recursive: true });
        this.cleanupStats.directoriesCreated++;
      }

      // Keep only the most recent 10 files of each type
      files.sort((a, b) => b.mtime - a.mtime);
      
      for (let i = 0; i < files.length; i++) {
        const file = files[i];
        const newPath = path.join(typeDir, path.basename(file.name));
        
        if (i < 10) {
          // Keep recent files, move to organized location
          if (file.path !== newPath) {
            fs.renameSync(file.path, newPath);
            console.log(`   📂 Organized: ${file.name} → ${type}/`);
          }
        } else {
          // Archive older files
          const archivePath = path.join('temp-reports', 'build-artifacts', path.basename(file.name));
          fs.renameSync(file.path, archivePath);
          this.cleanupStats.filesArchived++;
          console.log(`   📦 Archived old: ${file.name}`);
        }
      }
    }
  }

  categorizeReport(filename) {
    const lowerName = filename.toLowerCase();
    
    if (lowerName.includes('lighthouse')) return 'lighthouse';
    if (lowerName.includes('test') || lowerName.includes('vitest')) return 'testing';
    if (lowerName.includes('coverage')) return 'coverage';
    if (lowerName.includes('performance') || lowerName.includes('perf')) return 'performance';
    if (lowerName.includes('security') || lowerName.includes('audit')) return 'security';
    if (lowerName.includes('bundle') || lowerName.includes('webpack')) return 'bundling';
    if (lowerName.includes('flake') || lowerName.includes('stability')) return 'stability';
    if (lowerName.includes('conformance') || lowerName.includes('cegis')) return 'conformance';
    
    return 'general';
  }

  async generateCleanupReport() {
    console.log('📋 Generating cleanup report...');
    
    const report = {
      timestamp: new Date().toISOString(),
      summary: {
        totalFilesProcessed: this.cleanupStats.filesRemoved + this.cleanupStats.filesArchived,
        filesRemoved: this.cleanupStats.filesRemoved,
        filesArchived: this.cleanupStats.filesArchived,
        directoriesCreated: this.cleanupStats.directoriesCreated,
        spaceSaved: this.formatBytes(this.cleanupStats.spaceSaved)
      },
      recommendations: [
        'Run this cleanup script monthly to maintain project hygiene',
        'Configure build processes to auto-clean temporary files',
        'Consider implementing automated archival policies',
        'Monitor report generation to prevent accumulation'
      ],
      nextSteps: [
        'Review archived files before permanent deletion',
        'Update CI/CD to include cleanup steps',
        'Document cleanup procedures for team',
        'Set up monitoring for project size growth'
      ]
    };

    const reportPath = 'temp-reports/cleanup-report.json';
    fs.writeFileSync(reportPath, JSON.stringify(report, null, 2));
    
    console.log('\\n📊 Cleanup Summary:');
    console.log(`   Files Processed: ${report.summary.totalFilesProcessed}`);
    console.log(`   Files Removed: ${report.summary.filesRemoved}`);
    console.log(`   Files Archived: ${report.summary.filesArchived}`);
    console.log(`   Directories Created: ${report.summary.directoriesCreated}`);
    console.log(`   Space Saved: ${report.summary.spaceSaved}`);
    console.log(`\\n📄 Full report: ${reportPath}`);
    
    return report;
  }

  formatBytes(bytes) {
    if (bytes === 0) return '0 Bytes';
    
    const k = 1024;
    const sizes = ['Bytes', 'KB', 'MB', 'GB'];
    const i = Math.floor(Math.log(bytes) / Math.log(k));
    
    return parseFloat((bytes / Math.pow(k, i)).toFixed(2)) + ' ' + sizes[i];
  }

  async run() {
    console.log('🚀 Starting project cleanup and organization...');
    console.log(`   Working directory: ${this.rootDir}`);
    
    try {
      const analysis = await this.analyzeProjectStructure();
      
      console.log(`\\n📈 Analysis Results:`);
      console.log(`   Temporary files: ${analysis.temporaryFiles.length}`);
      console.log(`   Report files: ${analysis.reportFiles.length}`);
      console.log(`   Large files: ${analysis.largeFiles.length}`);
      
      await this.createArchiveStructure();
      await this.archiveTemporaryFiles(analysis);
      await this.cleanupBuildArtifacts();
      await this.optimizeReportsDirectory();
      
      const report = await this.generateCleanupReport();
      
      console.log('\\n✅ Project cleanup completed successfully!');
      
      return report;
      
    } catch (error) {
      console.error(`❌ Cleanup failed: ${error.message}`);
      throw error;
    }
  }
}

// CLI execution
if (import.meta.url === `file://${process.argv[1]}`) {
  const cleaner = new ProjectCleaner();
  
  cleaner.run()
    .then(() => {
      console.log('\\n🎉 All cleanup tasks completed!');
      process.exit(0);
    })
    .catch((error) => {
      console.error('💥 Cleanup failed:', error.message);
      process.exit(1);
    });
}

export { ProjectCleaner };