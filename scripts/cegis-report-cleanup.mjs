#!/usr/bin/env node

/**
 * CEGIS Report Cleanup Script
 * Organizes and archives CEGIS report files for better project management
 */

import fs from 'fs';
import fsp from 'fs/promises';
import path from 'path';
import { pathToFileURL } from 'url';

class CEGISReportCleanup {
  constructor() {
    this.archiveDir = './temp-reports/cegis-archives';
    this.summaryFile = './temp-reports/cegis-cleanup-summary.json';
    this.keepLatest = 5; // Keep only latest 5 reports in root
  }

  async createArchiveDirectory() {
    console.log('📁 Creating archive directory...');

    await fsp.mkdir('./temp-reports', { recursive: true });
    await fsp.mkdir(this.archiveDir, { recursive: true });

    console.log(`✅ Archive directory created: ${this.archiveDir}`);
  }

  async analyzeReports() {
    console.log('🔍 Analyzing CEGIS reports...');
    
    const reportFiles = fs.readdirSync('.')
      .filter(file => file.startsWith('cegis-report-') && file.endsWith('.json'))
      .map(file => {
        const stats = fs.statSync(file);
        const content = JSON.parse(fs.readFileSync(file, 'utf8'));
        
        return {
          filename: file,
          size: stats.size,
          created: stats.birthtime,
          modified: stats.mtime,
          timestamp: content.timestamp,
          failures: content.failures || 0,
          appliedFixes: content.appliedFixes?.length || 0,
          success: content.summary?.success || false
        };
      })
      .sort((a, b) => new Date(b.timestamp) - new Date(a.timestamp));

    console.log(`📊 Found ${reportFiles.length} CEGIS report files`);
    
    return reportFiles;
  }

  async categorizeReports(reports) {
    console.log('📋 Categorizing reports...');
    
    const categories = {
      successful: reports.filter(r => r.success && r.failures === 0),
      withFailures: reports.filter(r => r.failures > 0),
      withFixes: reports.filter(r => r.appliedFixes > 0),
      recent: reports.slice(0, this.keepLatest),
      archive: reports.slice(this.keepLatest)
    };

    console.log(`   ✅ Successful reports: ${categories.successful.length}`);
    console.log(`   ❌ Reports with failures: ${categories.withFailures.length}`);
    console.log(`   🔧 Reports with fixes: ${categories.withFixes.length}`);
    console.log(`   📅 Recent (keep in root): ${categories.recent.length}`);
    console.log(`   📦 To archive: ${categories.archive.length}`);
    
    return categories;
  }

  async archiveOldReports(categories) {
    console.log('📦 Archiving old reports...');
    
    let archivedCount = 0;
    
    for (const report of categories.archive) {
      const sourcePath = report.filename;
      const destPath = path.join(this.archiveDir, report.filename);
      
      try {
        await fsp.rename(sourcePath, destPath);
        archivedCount++;
      } catch (error) {
        console.warn(`⚠️ Failed to archive ${report.filename}: ${error.message}`);
      }
    }
    
    console.log(`✅ Archived ${archivedCount} reports to ${this.archiveDir}`);
    return archivedCount;
  }

  async generateCleanupSummary(reports, categories, archivedCount) {
    console.log('📄 Generating cleanup summary...');
    
    const summary = {
      cleanupDate: new Date().toISOString(),
      totalReportsFound: reports.length,
      archivedReports: archivedCount,
      keptInRoot: categories.recent.length,
      statistics: {
        successfulRuns: categories.successful.length,
        runsWithFailures: categories.withFailures.length,
        runsWithFixes: categories.withFixes.length,
        totalFailures: reports.reduce((sum, r) => sum + r.failures, 0),
        totalFixes: reports.reduce((sum, r) => sum + r.appliedFixes, 0)
      },
      dateRange: {
        earliest: reports[reports.length - 1]?.timestamp,
        latest: reports[0]?.timestamp
      },
      recentReports: categories.recent.map(r => ({
        filename: r.filename,
        timestamp: r.timestamp,
        success: r.success,
        failures: r.failures,
        fixes: r.appliedFixes
      })),
      archivePath: this.archiveDir,
      recommendations: [
        'Monitor recent reports for patterns in failures',
        'Review archived reports periodically for historical analysis',
        'Consider implementing automated report retention policies',
        'Set up alerts for reports with high failure rates'
      ]
    };

    fs.writeFileSync(this.summaryFile, JSON.stringify(summary, null, 2));
    console.log(`📊 Cleanup summary saved: ${this.summaryFile}`);
    
    return summary;
  }

  async displaySummary(summary) {
    console.log('\n📋 CEGIS Report Cleanup Summary:');
    console.log(`   📁 Total reports processed: ${summary.totalReportsFound}`);
    console.log(`   📦 Reports archived: ${summary.archivedReports}`);
    console.log(`   📍 Reports kept in root: ${summary.keptInRoot}`);
    console.log(`   ✅ Successful runs: ${summary.statistics.successfulRuns}`);
    console.log(`   ❌ Runs with failures: ${summary.statistics.runsWithFailures}`);
    console.log(`   🔧 Runs with fixes: ${summary.statistics.runsWithFixes}`);
    
    if (summary.dateRange.earliest && summary.dateRange.latest) {
      const earliest = new Date(summary.dateRange.earliest).toLocaleDateString();
      const latest = new Date(summary.dateRange.latest).toLocaleDateString();
      console.log(`   📅 Date range: ${earliest} to ${latest}`);
    }
    
    console.log('\n💡 Recommendations:');
    summary.recommendations.forEach(rec => {
      console.log(`   • ${rec}`);
    });
    
    console.log(`\n📁 Archived reports location: ${this.archiveDir}`);
    console.log(`📄 Detailed summary: ${this.summaryFile}`);
  }

  async updateGitignore() {
    console.log('📝 Updating .gitignore...');
    
    const gitignorePath = './.gitignore';
    const entriesToAdd = [
      'cegis-report-*.json',
      'temp-reports/',
      '# CEGIS report files - generated during testing'
    ];
    
    let gitignoreContent = '';
    try {
      gitignoreContent = await fsp.readFile(gitignorePath, 'utf8');
    } catch (error) {
      if (error?.code !== 'ENOENT') throw error;
    }
    
    let updated = false;
    for (const entry of entriesToAdd) {
      if (!gitignoreContent.includes(entry)) {
        gitignoreContent += `\n${entry}`;
        updated = true;
      }
    }
    
    if (updated) {
      fs.writeFileSync(gitignorePath, gitignoreContent);
      console.log('✅ Updated .gitignore with CEGIS report patterns');
    } else {
      console.log('ℹ️ .gitignore already contains CEGIS report patterns');
    }
  }
}

async function main() {
  const cleanup = new CEGISReportCleanup();
  
  try {
    console.log('🚀 Starting CEGIS report cleanup...\n');
    
    await cleanup.createArchiveDirectory();
    
    const reports = await cleanup.analyzeReports();
    if (reports.length === 0) {
      console.log('ℹ️ No CEGIS reports found to clean up');
      return;
    }
    
    const categories = await cleanup.categorizeReports(reports);
    const archivedCount = await cleanup.archiveOldReports(categories);
    const summary = await cleanup.generateCleanupSummary(reports, categories, archivedCount);
    
    await cleanup.displaySummary(summary);
    await cleanup.updateGitignore();
    
    console.log('\n✅ CEGIS report cleanup completed successfully!');
    
  } catch (error) {
    console.error(`❌ Error during cleanup: ${error.message}`);
    process.exit(1);
  }
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  main();
}

export { CEGISReportCleanup };
