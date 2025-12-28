/**
 * HTML Test Reporter
 * Phase 2.3: Generate comprehensive HTML reports for test execution results
 */

import { promises as fs } from 'fs';
import { dirname } from 'path';
import type {
  TestReporter,
  TestExecutionSummary,
  TestResult,
  TestStatus
} from '../types.js';

export class HTMLTestReporter implements TestReporter {
  readonly name = 'HTML Reporter';
  readonly format = 'html';

  /**
   * Generate HTML test report
   */
  async generateReport(summary: TestExecutionSummary): Promise<string> {
    const html = `
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Test Execution Report</title>
    ${this.generateStyles()}
    ${this.generateScripts()}
</head>
<body>
    <div class="container">
        ${this.generateHeader(summary)}
        ${this.generateSummaryCards(summary)}
        ${this.generateChartsSection(summary)}
        ${this.generateTestResults(summary)}
        ${this.generateFailures(summary)}
        ${this.generateArtifacts(summary)}
        ${this.generateFooter(summary)}
    </div>
</body>
</html>`;

    return html.trim();
  }

  /**
   * Save report to file
   */
  async saveReport(content: string, filePath: string): Promise<void> {
    await fs.mkdir(dirname(filePath), { recursive: true });
    await fs.writeFile(filePath, content, 'utf-8');
    
    // Copy static assets if needed
    await this.copyAssets(dirname(filePath));
  }

  /**
   * Generate CSS styles
   */
  private generateStyles(): string {
    return `
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }

        body {
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            line-height: 1.6;
            color: #333;
            background-color: #f8f9fa;
        }

        .container {
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
        }

        .header {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 2rem;
            border-radius: 10px;
            margin-bottom: 2rem;
            box-shadow: 0 4px 6px rgba(0, 0, 0, 0.1);
        }

        .header h1 {
            font-size: 2.5rem;
            margin-bottom: 0.5rem;
        }

        .header .subtitle {
            font-size: 1.1rem;
            opacity: 0.9;
        }

        .summary-cards {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 1rem;
            margin-bottom: 2rem;
        }

        .summary-card {
            background: white;
            padding: 1.5rem;
            border-radius: 10px;
            box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
            text-align: center;
            border-left: 4px solid;
        }

        .summary-card.total { border-left-color: #6c757d; }
        .summary-card.passed { border-left-color: #28a745; }
        .summary-card.failed { border-left-color: #dc3545; }
        .summary-card.skipped { border-left-color: #ffc107; }
        .summary-card.error { border-left-color: #fd7e14; }

        .summary-card .number {
            font-size: 2.5rem;
            font-weight: bold;
            margin-bottom: 0.5rem;
        }

        .summary-card.total .number { color: #6c757d; }
        .summary-card.passed .number { color: #28a745; }
        .summary-card.failed .number { color: #dc3545; }
        .summary-card.skipped .number { color: #ffc107; }
        .summary-card.error .number { color: #fd7e14; }

        .summary-card .label {
            color: #6c757d;
            font-size: 0.9rem;
            text-transform: uppercase;
            letter-spacing: 1px;
        }

        .section {
            background: white;
            border-radius: 10px;
            padding: 1.5rem;
            margin-bottom: 2rem;
            box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
        }

        .section h2 {
            margin-bottom: 1rem;
            color: #495057;
            border-bottom: 2px solid #e9ecef;
            padding-bottom: 0.5rem;
        }

        .charts-section {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 2rem;
            margin-bottom: 2rem;
        }

        .chart-container {
            background: white;
            padding: 1.5rem;
            border-radius: 10px;
            box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
            text-align: center;
        }

        .test-results {
            overflow-x: auto;
        }

        .test-table {
            width: 100%;
            border-collapse: collapse;
            margin-top: 1rem;
        }

        .test-table th,
        .test-table td {
            padding: 0.75rem;
            text-align: left;
            border-bottom: 1px solid #dee2e6;
        }

        .test-table th {
            background-color: #f8f9fa;
            font-weight: 600;
            color: #495057;
        }

        .test-table tbody tr:hover {
            background-color: #f8f9fa;
        }

        .status-badge {
            display: inline-block;
            padding: 0.25rem 0.75rem;
            border-radius: 20px;
            font-size: 0.8rem;
            font-weight: 600;
            text-transform: uppercase;
        }

        .status-passed { background-color: #d4edda; color: #155724; }
        .status-failed { background-color: #f8d7da; color: #721c24; }
        .status-skipped { background-color: #fff3cd; color: #856404; }
        .status-error { background-color: #f5c6cb; color: #721c24; }
        .status-timeout { background-color: #ffeaa7; color: #856404; }

        .duration {
            color: #6c757d;
            font-size: 0.9rem;
        }

        .failure-item {
            background: #f8f9fa;
            border: 1px solid #dee2e6;
            border-radius: 5px;
            padding: 1rem;
            margin-bottom: 1rem;
        }

        .failure-header {
            font-weight: 600;
            color: #dc3545;
            margin-bottom: 0.5rem;
        }

        .failure-message {
            color: #495057;
            margin-bottom: 0.5rem;
            font-family: monospace;
            background: white;
            padding: 0.5rem;
            border-radius: 3px;
            border-left: 3px solid #dc3545;
        }

        .stack-trace {
            background: #f1f3f4;
            border-radius: 3px;
            padding: 0.5rem;
            font-family: 'Courier New', monospace;
            font-size: 0.8rem;
            color: #5f6368;
            white-space: pre-wrap;
            max-height: 200px;
            overflow-y: auto;
        }

        .artifacts-grid {
            display: grid;
            grid-template-columns: repeat(auto-fill, minmax(200px, 1fr));
            gap: 1rem;
            margin-top: 1rem;
        }

        .artifact-item {
            background: #f8f9fa;
            border: 1px solid #dee2e6;
            border-radius: 5px;
            padding: 1rem;
            text-align: center;
        }

        .artifact-icon {
            font-size: 2rem;
            margin-bottom: 0.5rem;
        }

        .artifact-name {
            font-weight: 600;
            margin-bottom: 0.25rem;
            word-break: break-all;
        }

        .artifact-size {
            color: #6c757d;
            font-size: 0.8rem;
        }

        .footer {
            text-align: center;
            color: #6c757d;
            margin-top: 2rem;
            padding-top: 1rem;
            border-top: 1px solid #dee2e6;
        }

        .collapsible {
            cursor: pointer;
            user-select: none;
        }

        .collapsible:hover {
            background-color: #f8f9fa;
        }

        .collapsible-content {
            display: none;
            padding-top: 1rem;
        }

        .collapsible-content.show {
            display: block;
        }

        .filter-bar {
            margin-bottom: 1rem;
            display: flex;
            gap: 1rem;
            align-items: center;
            flex-wrap: wrap;
        }

        .filter-btn {
            padding: 0.5rem 1rem;
            border: 1px solid #dee2e6;
            background: white;
            border-radius: 5px;
            cursor: pointer;
            transition: all 0.3s;
        }

        .filter-btn.active {
            background: #007bff;
            color: white;
            border-color: #007bff;
        }

        .progress-bar {
            width: 100%;
            height: 10px;
            background: #e9ecef;
            border-radius: 5px;
            overflow: hidden;
            margin: 1rem 0;
        }

        .progress-fill {
            height: 100%;
            background: linear-gradient(90deg, #28a745, #20c997);
            transition: width 0.3s ease;
        }

        @media (max-width: 768px) {
            .charts-section {
                grid-template-columns: 1fr;
            }
            
            .summary-cards {
                grid-template-columns: repeat(2, 1fr);
            }
            
            .filter-bar {
                justify-content: center;
            }
        }
    </style>`;
  }

  /**
   * Generate JavaScript
   */
  private generateScripts(): string {
    return `
    <script>
        // Toggle collapsible content
        function toggleCollapsible(element) {
            const content = element.nextElementSibling;
            content.classList.toggle('show');
            
            const icon = element.querySelector('.toggle-icon');
            if (icon) {
                icon.textContent = content.classList.contains('show') ? '▼' : '▶';
            }
        }

        // Filter tests
        function filterTests(status) {
            const rows = document.querySelectorAll('.test-table tbody tr');
            const buttons = document.querySelectorAll('.filter-btn');
            
            // Update active button
            buttons.forEach(btn => {
                btn.classList.remove('active');
                if (btn.textContent.toLowerCase().includes(status) || 
                    (status === 'all' && btn.textContent.toLowerCase().includes('all'))) {
                    btn.classList.add('active');
                }
            });
            
            // Filter rows
            rows.forEach(row => {
                const statusCell = row.querySelector('.status-badge');
                if (status === 'all' || statusCell.classList.contains('status-' + status)) {
                    row.style.display = '';
                } else {
                    row.style.display = 'none';
                }
            });
            
            // Update counters
            updateVisibleCount();
        }

        // Update visible test count
        function updateVisibleCount() {
            const visibleRows = document.querySelectorAll('.test-table tbody tr:not([style*="display: none"])');
            const countElement = document.getElementById('visible-count');
            if (countElement) {
                countElement.textContent = visibleRows.length;
            }
        }

        // Initialize page
        document.addEventListener('DOMContentLoaded', function() {
            // Set initial filter
            filterTests('all');
            
            // Add collapsible functionality
            document.querySelectorAll('.collapsible').forEach(element => {
                element.addEventListener('click', () => toggleCollapsible(element));
            });
            
            // Generate charts if Chart.js is available
            if (typeof Chart !== 'undefined') {
                generateCharts();
            }
        });

        // Generate charts (placeholder - would need Chart.js library)
        function generateCharts() {
            // This would generate actual charts with Chart.js
            console.log('Charts would be generated here with Chart.js');
        }
    </script>`;
  }

  /**
   * Generate report header
   */
  private generateHeader(summary: TestExecutionSummary): string {
    return `
    <div class="header">
        <h1>📊 Test Execution Report</h1>
        <div class="subtitle">
            Environment: ${summary.environment} | 
            Duration: ${this.formatDuration(summary.duration)} | 
            Generated: ${new Date(summary.endTime).toLocaleString()}
        </div>
    </div>`;
  }

  /**
   * Generate summary cards
   */
  private generateSummaryCards(summary: TestExecutionSummary): string {
    const stats = summary.statistics;
    
    return `
    <div class="summary-cards">
        <div class="summary-card total">
            <div class="number">${stats.total}</div>
            <div class="label">Total Tests</div>
        </div>
        <div class="summary-card passed">
            <div class="number">${stats.passed}</div>
            <div class="label">Passed</div>
        </div>
        <div class="summary-card failed">
            <div class="number">${stats.failed}</div>
            <div class="label">Failed</div>
        </div>
        <div class="summary-card skipped">
            <div class="number">${stats.skipped}</div>
            <div class="label">Skipped</div>
        </div>
        <div class="summary-card error">
            <div class="number">${stats.error}</div>
            <div class="label">Errors</div>
        </div>
    </div>
    
    <div class="section">
        <h2>📈 Pass Rate</h2>
        <div class="progress-bar">
            <div class="progress-fill" style="width: ${stats.passRate.toFixed(1)}%"></div>
        </div>
        <div style="text-align: center; margin-top: 0.5rem; font-weight: 600; color: #495057;">
            ${stats.passRate.toFixed(1)}% Pass Rate
        </div>
    </div>`;
  }

  /**
   * Generate charts section
   */
  private generateChartsSection(summary: TestExecutionSummary): string {
    return `
    <div class="charts-section">
        <div class="chart-container">
            <h3>Test Results Distribution</h3>
            <div id="results-chart" style="height: 300px;">
                ${this.generatePieChart(summary.statistics)}
            </div>
        </div>
        <div class="chart-container">
            <h3>Execution Timeline</h3>
            <div id="timeline-chart" style="height: 300px;">
                <p style="color: #6c757d; text-align: center; padding-top: 2rem;">
                    Timeline visualization would appear here with Chart.js
                </p>
            </div>
        </div>
    </div>`;
  }

  /**
   * Generate simple pie chart representation
   */
  private generatePieChart(stats: any): string {
    const total = stats.total;
    if (total === 0) {
      return '<p style="color: #6c757d; text-align: center; padding-top: 2rem;">No test data available</p>';
    }

    const passedAngle = (stats.passed / total) * 360;
    const failedAngle = (stats.failed / total) * 360;
    const skippedAngle = (stats.skipped / total) * 360;
    
    return `
    <svg width="200" height="200" viewBox="0 0 42 42" style="margin: 0 auto; display: block;">
        <circle cx="21" cy="21" r="15.915" fill="transparent" stroke="#28a745" 
                stroke-width="3" stroke-dasharray="${stats.passed / total * 100} ${100 - stats.passed / total * 100}" 
                stroke-dashoffset="25"></circle>
        <circle cx="21" cy="21" r="15.915" fill="transparent" stroke="#dc3545" 
                stroke-width="3" stroke-dasharray="${stats.failed / total * 100} ${100 - stats.failed / total * 100}" 
                stroke-dashoffset="${25 - stats.passed / total * 100}"></circle>
    </svg>
    <div style="text-align: center; margin-top: 1rem;">
        <div style="display: inline-block; margin: 0 1rem;">
            <span style="display: inline-block; width: 12px; height: 12px; background: #28a745; margin-right: 5px;"></span>
            Passed (${stats.passed})
        </div>
        <div style="display: inline-block; margin: 0 1rem;">
            <span style="display: inline-block; width: 12px; height: 12px; background: #dc3545; margin-right: 5px;"></span>
            Failed (${stats.failed})
        </div>
    </div>`;
  }

  /**
   * Generate test results table
   */
  private generateTestResults(summary: TestExecutionSummary): string {
    const filterBar = `
    <div class="filter-bar">
        <span>Filter by status:</span>
        <button class="filter-btn active" onclick="filterTests('all')">All (<span id="visible-count">${summary.results.length}</span>)</button>
        <button class="filter-btn" onclick="filterTests('passed')">Passed (${summary.statistics.passed})</button>
        <button class="filter-btn" onclick="filterTests('failed')">Failed (${summary.statistics.failed})</button>
        <button class="filter-btn" onclick="filterTests('skipped')">Skipped (${summary.statistics.skipped})</button>
        <button class="filter-btn" onclick="filterTests('error')">Error (${summary.statistics.error})</button>
    </div>`;

    const tableRows = summary.results.map(result => `
        <tr>
            <td>
                <div class="collapsible" style="font-weight: 600;">
                    <span class="toggle-icon">▶</span> Test ${result.testId}
                </div>
                <div class="collapsible-content">
                    <strong>Steps:</strong> ${result.steps.length}<br>
                    <strong>Started:</strong> ${new Date(result.startTime).toLocaleString()}<br>
                    ${result.error ? `<strong>Error:</strong> ${result.error}<br>` : ''}
                    ${result.logs.length > 0 ? `<strong>Logs:</strong><br>${result.logs.map(log => `• ${log}`).join('<br>')}` : ''}
                </div>
            </td>
            <td>
                <span class="status-badge status-${result.status}">${result.status}</span>
            </td>
            <td class="duration">${this.formatDuration(result.duration)}</td>
            <td>${result.steps.filter(s => s.status === 'passed').length}/${result.steps.length}</td>
            <td>${result.screenshots?.length || 0}</td>
        </tr>
    `).join('');

    return `
    <div class="section">
        <h2>🧪 Test Results</h2>
        ${filterBar}
        <div class="test-results">
            <table class="test-table">
                <thead>
                    <tr>
                        <th>Test</th>
                        <th>Status</th>
                        <th>Duration</th>
                        <th>Steps</th>
                        <th>Screenshots</th>
                    </tr>
                </thead>
                <tbody>
                    ${tableRows}
                </tbody>
            </table>
        </div>
    </div>`;
  }

  /**
   * Generate failures section
   */
  private generateFailures(summary: TestExecutionSummary): string {
    if (summary.failures.length === 0) {
      return `
      <div class="section">
          <h2>❌ Failures</h2>
          <p style="color: #28a745; text-align: center; padding: 2rem;">
              🎉 No failures detected! All tests passed successfully.
          </p>
      </div>`;
    }

    const failureItems = summary.failures.map((failure, index) => `
        <div class="failure-item">
            <div class="failure-header">
                ${index + 1}. ${failure.testName} (ID: ${failure.testId})
            </div>
            <div class="failure-message">
                ${this.escapeHtml(failure.error)}
            </div>
            ${failure.stackTrace ? `
                <div class="collapsible" style="color: #6c757d; cursor: pointer; margin-top: 0.5rem;">
                    <span class="toggle-icon">▶</span> Show Stack Trace
                </div>
                <div class="collapsible-content">
                    <div class="stack-trace">${this.escapeHtml(failure.stackTrace)}</div>
                </div>
            ` : ''}
        </div>
    `).join('');

    return `
    <div class="section">
        <h2>❌ Failures (${summary.failures.length})</h2>
        ${failureItems}
    </div>`;
  }

  /**
   * Generate artifacts section
   */
  private generateArtifacts(summary: TestExecutionSummary): string {
    if (summary.artifacts.length === 0) {
      return `
      <div class="section">
          <h2>📎 Test Artifacts</h2>
          <p style="color: #6c757d; text-align: center; padding: 2rem;">
              No artifacts were generated during this test run.
          </p>
      </div>`;
    }

    const artifactItems = summary.artifacts.map(artifact => {
      const icon = this.getArtifactIcon(artifact.name);
      const size = this.formatFileSize(artifact.size);
      
      return `
        <div class="artifact-item">
            <div class="artifact-icon">${icon}</div>
            <div class="artifact-name">${artifact.name}</div>
            <div class="artifact-size">${size}</div>
        </div>`;
    }).join('');

    return `
    <div class="section">
        <h2>📎 Test Artifacts (${summary.artifacts.length})</h2>
        <div class="artifacts-grid">
            ${artifactItems}
        </div>
    </div>`;
  }

  /**
   * Generate report footer
   */
  private generateFooter(summary: TestExecutionSummary): string {
    return `
    <div class="footer">
        <p>Generated by AE Framework Integration Testing System</p>
        <p>Report ID: ${summary.id}</p>
        <p>Node.js ${summary.metadata.nodeVersion || 'Unknown'} on ${summary.metadata.platform || 'Unknown'}</p>
    </div>`;
  }

  /**
   * Get icon for artifact type
   */
  private getArtifactIcon(fileName: string): string {
    const ext = fileName.split('.').pop()?.toLowerCase();
    
    switch (ext) {
      case 'png':
      case 'jpg':
      case 'jpeg':
      case 'gif':
        return '🖼️';
      case 'mp4':
      case 'webm':
      case 'mov':
        return '🎥';
      case 'log':
      case 'txt':
        return '📄';
      case 'json':
        return '📋';
      case 'html':
        return '🌐';
      case 'zip':
      case 'tar':
      case 'gz':
        return '📦';
      default:
        return '📎';
    }
  }

  /**
   * Format duration in milliseconds
   */
  private formatDuration(ms: number): string {
    if (ms < 1000) {
      return `${ms}ms`;
    } else if (ms < 60000) {
      return `${(ms / 1000).toFixed(1)}s`;
    } else {
      const minutes = Math.floor(ms / 60000);
      const seconds = ((ms % 60000) / 1000).toFixed(0);
      return `${minutes}m ${seconds}s`;
    }
  }

  /**
   * Format file size in bytes
   */
  private formatFileSize(bytes: number): string {
    const sizes = ['B', 'KB', 'MB', 'GB'];
    if (bytes === 0) return '0 B';
    
    const i = Math.floor(Math.log(bytes) / Math.log(1024));
    return `${(bytes / Math.pow(1024, i)).toFixed(1)} ${sizes[i]}`;
  }

  /**
   * Escape HTML entities
   */
  private escapeHtml(text: string): string {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
  }

  /**
   * Copy static assets
   */
  private async copyAssets(outputDir: string): Promise<void> {
    // In a real implementation, you might copy CSS, JS, and image assets
    // For now, everything is inline
  }
}
