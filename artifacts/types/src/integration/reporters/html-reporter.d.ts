/**
 * HTML Test Reporter
 * Phase 2.3: Generate comprehensive HTML reports for test execution results
 */
import { TestReporter, TestExecutionSummary } from '../types.js';
export declare class HTMLTestReporter implements TestReporter {
    readonly name = "HTML Reporter";
    readonly format = "html";
    /**
     * Generate HTML test report
     */
    generateReport(summary: TestExecutionSummary): Promise<string>;
    /**
     * Save report to file
     */
    saveReport(content: string, filePath: string): Promise<void>;
    /**
     * Generate CSS styles
     */
    private generateStyles;
    /**
     * Generate JavaScript
     */
    private generateScripts;
    /**
     * Generate report header
     */
    private generateHeader;
    /**
     * Generate summary cards
     */
    private generateSummaryCards;
    /**
     * Generate charts section
     */
    private generateChartsSection;
    /**
     * Generate simple pie chart representation
     */
    private generatePieChart;
    /**
     * Generate test results table
     */
    private generateTestResults;
    /**
     * Generate failures section
     */
    private generateFailures;
    /**
     * Generate artifacts section
     */
    private generateArtifacts;
    /**
     * Generate report footer
     */
    private generateFooter;
    /**
     * Get icon for artifact type
     */
    private getArtifactIcon;
    /**
     * Format duration in milliseconds
     */
    private formatDuration;
    /**
     * Format file size in bytes
     */
    private formatFileSize;
    /**
     * Escape HTML entities
     */
    private escapeHtml;
    /**
     * Copy static assets
     */
    private copyAssets;
}
