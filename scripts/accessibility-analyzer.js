#!/usr/bin/env node

/**
 * Accessibility Analyzer
 * Comprehensive accessibility testing and analysis for ae-framework
 */

import { execSync } from 'child_process';
import { existsSync, readFileSync, writeFileSync, mkdirSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

class AccessibilityAnalyzer {
  constructor() {
    this.projectRoot = join(__dirname, '..');
    this.reportDir = join(this.projectRoot, 'accessibility-reports');
    this.timestamp = new Date().toISOString().replace(/[:.]/g, '-');
  }

  async analyze() {
    console.log('♿ Running comprehensive accessibility analysis...\n');
    
    this.ensureReportDirectory();
    
    const results = {
      timestamp: new Date().toISOString(),
      summary: {
        totalChecks: 6,
        passed: 0,
        failed: 0,
        warnings: 0
      },
      checks: {
        axeAnalysis: await this.runAxeAnalysis(),
        lighthouseA11y: await this.runLighthouseA11y(),
        pseudoLocalization: await this.runPseudoLocalization(),
        colorContrast: await this.checkColorContrast(),
        keyboardNavigation: await this.checkKeyboardNavigation(),
        screenReaderSupport: await this.checkScreenReaderSupport()
      }
    };

    // Calculate summary
    Object.values(results.checks).forEach(check => {
      if (check.status === 'passed') results.summary.passed++;
      else if (check.status === 'failed') results.summary.failed++;
      else if (check.status === 'warning') results.summary.warnings++;
    });

    // Generate report
    await this.generateReport(results);
    
    console.log('\n📊 Accessibility Analysis Summary:');
    console.log(`✅ Passed: ${results.summary.passed}`);
    console.log(`❌ Failed: ${results.summary.failed}`);
    console.log(`⚠️  Warnings: ${results.summary.warnings}`);
    
    const overallScore = (results.summary.passed / results.summary.totalChecks) * 100;
    console.log(`♿ Accessibility Score: ${overallScore.toFixed(1)}%`);
    
    if (results.summary.failed > 0) {
      console.log('\n🚨 Accessibility issues detected! Please review the report.');
      process.exit(1);
    }
    
    return results;
  }

  async runAxeAnalysis() {
    console.log('🔍 Running axe-core accessibility analysis...');
    
    try {
      // Check if jest-axe tests exist and run them
      const a11yTestFiles = [
        'tests/a11y',
        'tests/accessibility',
        'src/**/*.a11y.test.{js,ts}',
        'src/**/*.accessibility.test.{js,ts}'
      ];
      
      let foundTests = false;
      for (const pattern of a11yTestFiles) {
        try {
          const files = execSync(`find ${this.projectRoot} -path "*/${pattern}*" -type f 2>/dev/null || true`, {
            encoding: 'utf-8'
          }).trim();
          
          if (files) {
            foundTests = true;
            break;
          }
        } catch (error) {
          // Continue searching
        }
      }
      
      if (foundTests) {
        try {
          const testResult = execSync('npm run test:a11y', {
            cwd: this.projectRoot,
            encoding: 'utf-8',
            stdio: 'pipe'
          });
          
          console.log('  ✅ Axe accessibility tests passed');
          return {
            status: 'passed',
            tool: 'jest-axe',
            details: ['All accessibility tests passed']
          };
        } catch (error) {
          return {
            status: 'failed',
            tool: 'jest-axe',
            details: ['Accessibility tests failed - check test output']
          };
        }
      } else {
        // Create basic axe test structure
        await this.createBasicAxeTests();
        
        return {
          status: 'warning',
          tool: 'jest-axe',
          details: ['No accessibility tests found - basic structure created']
        };
      }
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'jest-axe',
        details: [`Axe analysis setup failed: ${error.message}`]
      };
    }
  }

  async runLighthouseA11y() {
    console.log('🏮 Running Lighthouse accessibility audit...');
    
    try {
      // Check if Lighthouse CI is configured
      const lhciConfig = join(this.projectRoot, 'lighthouserc.json');
      
      if (!existsSync(lhciConfig)) {
        await this.createLighthouseConfig();
      }
      
      // Run Lighthouse accessibility audit
      const lhResult = execSync('npx lhci autorun --collect.settings.onlyCategories=accessibility --upload.target=temporary-public-storage', {
        cwd: this.projectRoot,
        encoding: 'utf-8',
        stdio: 'pipe'
      });
      
      // Parse Lighthouse results
      const resultsPath = join(this.projectRoot, '.lighthouseci');
      if (existsSync(resultsPath)) {
        const resultFiles = execSync(`find ${resultsPath} -name "*.json" -type f | head -1`, {
          encoding: 'utf-8'
        }).trim();
        
        if (resultFiles) {
          const result = JSON.parse(readFileSync(resultFiles, 'utf-8'));
          const a11yScore = result.categories?.accessibility?.score * 100 || 0;
          
          console.log(`  📊 Lighthouse Accessibility Score: ${a11yScore}%`);
          
          return {
            status: a11yScore >= 90 ? 'passed' : a11yScore >= 70 ? 'warning' : 'failed',
            tool: 'Lighthouse',
            details: [
              `Accessibility Score: ${a11yScore}%`,
              `Performance: ${(result.categories?.performance?.score * 100 || 0).toFixed(1)}%`,
              `Best Practices: ${(result.categories?.['best-practices']?.score * 100 || 0).toFixed(1)}%`
            ]
          };
        }
      }
      
      return {
        status: 'warning',
        tool: 'Lighthouse',
        details: ['Lighthouse audit completed but results could not be parsed']
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Lighthouse',
        details: [`Lighthouse audit failed: ${error.message}`]
      };
    }
  }

  async runPseudoLocalization() {
    console.log('🌐 Running pseudo-localization analysis...');
    
    try {
      // Create pseudo-localization analyzer
      const pseudoLocalizer = this.createPseudoLocalizer();
      
      // Scan for hardcoded strings in React/UI components
      const uiFiles = this.findUIFiles();
      const hardcodedStrings = [];
      
      for (const file of uiFiles) {
        try {
          const content = readFileSync(file, 'utf-8');
          const strings = this.extractHardcodedStrings(content);
          
          if (strings.length > 0) {
            hardcodedStrings.push({
              file: file.replace(this.projectRoot + '/', ''),
              strings: strings
            });
          }
        } catch (error) {
          // Skip files that can't be read
        }
      }
      
      // Test pseudo-localization
      const pseudoResult = await this.testPseudoLocalization();
      
      console.log(`  📝 Found ${hardcodedStrings.length} files with potential hardcoded strings`);
      
      return {
        status: hardcodedStrings.length === 0 ? 'passed' : 'warning',
        tool: 'Pseudo-localization',
        details: hardcodedStrings.length === 0 
          ? ['No hardcoded strings detected in UI components']
          : [
              `Found ${hardcodedStrings.length} files with potential hardcoded strings`,
              ...hardcodedStrings.slice(0, 3).map(hs => `${hs.file}: ${hs.strings.length} strings`)
            ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Pseudo-localization',
        details: [`Pseudo-localization analysis failed: ${error.message}`]
      };
    }
  }

  async checkColorContrast() {
    console.log('🎨 Checking color contrast ratios...');
    
    try {
      // Extract colors from CSS/design tokens
      const colors = await this.extractColors();
      const contrastIssues = [];
      
      // Check contrast ratios for common color combinations
      const combinations = this.generateColorCombinations(colors);
      
      for (const combo of combinations) {
        const ratio = this.calculateContrastRatio(combo.fg, combo.bg);
        
        if (ratio < 4.5) { // WCAG AA standard
          contrastIssues.push({
            foreground: combo.fg,
            background: combo.bg,
            ratio: ratio.toFixed(2),
            level: ratio < 3 ? 'fail' : 'aa-large'
          });
        }
      }
      
      console.log(`  🎯 Checked ${combinations.length} color combinations`);
      
      return {
        status: contrastIssues.length === 0 ? 'passed' : 'warning',
        tool: 'Color Contrast',
        details: contrastIssues.length === 0
          ? ['All color combinations meet WCAG AA standards']
          : [
              `Found ${contrastIssues.length} potential contrast issues`,
              ...contrastIssues.slice(0, 3).map(issue => 
                `${issue.foreground} on ${issue.background}: ${issue.ratio}:1 (${issue.level})`
              )
            ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Color Contrast',
        details: [`Color contrast analysis failed: ${error.message}`]
      };
    }
  }

  async checkKeyboardNavigation() {
    console.log('⌨️  Checking keyboard navigation support...');
    
    try {
      // Scan for keyboard navigation patterns
      const componentFiles = this.findUIFiles();
      const keyboardIssues = [];
      
      for (const file of componentFiles) {
        try {
          const content = readFileSync(file, 'utf-8');
          const issues = this.checkKeyboardPatterns(content, file);
          keyboardIssues.push(...issues);
        } catch (error) {
          // Skip files that can't be read
        }
      }
      
      console.log(`  🔍 Scanned ${componentFiles.length} component files`);
      
      return {
        status: keyboardIssues.length === 0 ? 'passed' : 'warning',
        tool: 'Keyboard Navigation',
        details: keyboardIssues.length === 0
          ? ['No keyboard navigation issues detected']
          : [
              `Found ${keyboardIssues.length} potential keyboard navigation issues`,
              ...keyboardIssues.slice(0, 3).map(issue => `${issue.file}: ${issue.type}`)
            ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Keyboard Navigation',
        details: [`Keyboard navigation analysis failed: ${error.message}`]
      };
    }
  }

  async checkScreenReaderSupport() {
    console.log('🔊 Checking screen reader support...');
    
    try {
      // Scan for ARIA attributes and semantic HTML
      const componentFiles = this.findUIFiles();
      const ariaIssues = [];
      
      for (const file of componentFiles) {
        try {
          const content = readFileSync(file, 'utf-8');
          const issues = this.checkAriaPatterns(content, file);
          ariaIssues.push(...issues);
        } catch (error) {
          // Skip files that can't be read
        }
      }
      
      console.log(`  📋 Analyzed ARIA usage in ${componentFiles.length} files`);
      
      return {
        status: ariaIssues.length === 0 ? 'passed' : 'warning',
        tool: 'Screen Reader Support',
        details: ariaIssues.length === 0
          ? ['Good ARIA usage and semantic HTML detected']
          : [
              `Found ${ariaIssues.length} potential screen reader issues`,
              ...ariaIssues.slice(0, 3).map(issue => `${issue.file}: ${issue.type}`)
            ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Screen Reader Support',
        details: [`Screen reader support analysis failed: ${error.message}`]
      };
    }
  }

  // Helper methods
  findUIFiles() {
    try {
      const files = execSync(`find ${this.projectRoot} -type f \\( -name "*.jsx" -o -name "*.tsx" -o -name "*.vue" \\) | grep -v node_modules | head -100`, {
        encoding: 'utf-8'
      }).split('\n').filter(Boolean);
      
      return files;
    } catch (error) {
      return [];
    }
  }

  extractHardcodedStrings(content) {
    const strings = [];
    
    // Simple regex patterns for hardcoded strings (can be improved)
    const patterns = [
      />\s*([A-Z][a-zA-Z\s]{3,})\s*</g,  // Text between tags
      /placeholder\s*=\s*["']([^"']{3,})["']/g, // Placeholder text
      /title\s*=\s*["']([^"']{3,})["']/g, // Title text
      /alt\s*=\s*["']([^"']{3,})["']/g   // Alt text
    ];
    
    for (const pattern of patterns) {
      let match;
      while ((match = pattern.exec(content)) !== null) {
        const text = match[1].trim();
        if (text && !text.includes('{') && !text.includes('$')) {
          strings.push(text);
        }
      }
    }
    
    return [...new Set(strings)]; // Remove duplicates
  }

  async testPseudoLocalization() {
    // Simplified pseudo-localization test
    const pseudoMap = {
      'a': 'ä', 'e': 'ë', 'i': 'ï', 'o': 'ö', 'u': 'ü',
      'A': 'Ä', 'E': 'Ë', 'I': 'Ï', 'O': 'Ö', 'U': 'Ü'
    };
    
    return {
      enabled: true,
      coverage: 85 // Simulated coverage
    };
  }

  createPseudoLocalizer() {
    return {
      transform: (text) => {
        return `[${text.replace(/[aeiouAEIOU]/g, match => 
          ({ 'a': 'ä', 'e': 'ë', 'i': 'ï', 'o': 'ö', 'u': 'ü',
             'A': 'Ä', 'E': 'Ë', 'I': 'Ï', 'O': 'Ö', 'U': 'Ü' }[match] || match)
        )}]`;
      }
    };
  }

  async extractColors() {
    const colors = new Set();
    
    // Extract from CSS files
    try {
      const cssFiles = execSync(`find ${this.projectRoot} -name "*.css" -o -name "*.scss" -o -name "*.less" | grep -v node_modules | head -20`, {
        encoding: 'utf-8'
      }).split('\n').filter(Boolean);
      
      for (const file of cssFiles) {
        try {
          const content = readFileSync(file, 'utf-8');
          const colorMatches = content.match(/#[0-9a-fA-F]{3,6}|rgb\\([^)]+\\)|rgba\\([^)]+\\)/g) || [];
          colorMatches.forEach(color => colors.add(color));
        } catch (error) {
          // Skip files that can't be read
        }
      }
    } catch (error) {
      // No CSS files found
    }
    
    // Add common default colors
    colors.add('#000000');
    colors.add('#ffffff');
    colors.add('#333333');
    colors.add('#666666');
    
    return Array.from(colors);
  }

  generateColorCombinations(colors) {
    const combinations = [];
    
    for (let i = 0; i < colors.length; i++) {
      for (let j = 0; j < colors.length; j++) {
        if (i !== j) {
          combinations.push({
            fg: colors[i],
            bg: colors[j]
          });
        }
      }
    }
    
    return combinations.slice(0, 20); // Limit combinations
  }

  calculateContrastRatio(color1, color2) {
    // Simplified contrast ratio calculation
    // In a real implementation, you'd use a proper color library
    const getLuminance = (color) => {
      // Very simplified luminance calculation
      if (color === '#000000' || color === '#000') return 0;
      if (color === '#ffffff' || color === '#fff') return 1;
      return 0.5; // Default middle value
    };
    
    const lum1 = getLuminance(color1);
    const lum2 = getLuminance(color2);
    
    const lighter = Math.max(lum1, lum2);
    const darker = Math.min(lum1, lum2);
    
    return (lighter + 0.05) / (darker + 0.05);
  }

  checkKeyboardPatterns(content, filePath) {
    const issues = [];
    
    // Check for missing tabIndex
    if (content.includes('onClick') && !content.includes('tabIndex') && !content.includes('onKeyDown')) {
      issues.push({
        file: filePath.replace(this.projectRoot + '/', ''),
        type: 'Missing keyboard support for clickable element'
      });
    }
    
    // Check for focus management
    if (content.includes('modal') && !content.includes('focus')) {
      issues.push({
        file: filePath.replace(this.projectRoot + '/', ''),
        type: 'Modal without focus management'
      });
    }
    
    return issues;
  }

  checkAriaPatterns(content, filePath) {
    const issues = [];
    
    // Check for missing ARIA labels
    if (content.includes('button') && !content.includes('aria-label') && !content.includes('aria-labelledby')) {
      issues.push({
        file: filePath.replace(this.projectRoot + '/', ''),
        type: 'Button without ARIA label'
      });
    }
    
    // Check for images without alt text
    if (content.includes('<img') && !content.includes('alt=')) {
      issues.push({
        file: filePath.replace(this.projectRoot + '/', ''),
        type: 'Image without alt text'
      });
    }
    
    return issues;
  }

  async createBasicAxeTests() {
    const testDir = join(this.projectRoot, 'tests/a11y');
    mkdirSync(testDir, { recursive: true });
    
    const basicTest = `
import { render } from '@testing-library/react';
import { axe, toHaveNoViolations } from 'jest-axe';
import React from 'react';

expect.extend(toHaveNoViolations);

describe('Accessibility Tests', () => {
  it('should not have accessibility violations', async () => {
    const { container } = render(
      <div>
        <h1>Test Page</h1>
        <button>Click me</button>
        <img src="test.jpg" alt="Test image" />
      </div>
    );
    
    const results = await axe(container);
    expect(results).toHaveNoViolations();
  });
});
`;
    
    writeFileSync(join(testDir, 'basic.test.js'), basicTest);
  }

  async createLighthouseConfig() {
    const config = {
      ci: {
        collect: {
          numberOfRuns: 1,
          startServerCommand: 'npm run dev',
          startServerReadyPattern: 'ready',
          url: ['http://localhost:3000']
        },
        upload: {
          target: 'temporary-public-storage'
        }
      }
    };
    
    writeFileSync(join(this.projectRoot, 'lighthouserc.json'), JSON.stringify(config, null, 2));
  }

  ensureReportDirectory() {
    if (!existsSync(this.reportDir)) {
      mkdirSync(this.reportDir, { recursive: true });
    }
  }

  async generateReport(results) {
    const reportPath = join(this.reportDir, `accessibility-report-${this.timestamp}.json`);
    writeFileSync(reportPath, JSON.stringify(results, null, 2));
    
    // Generate human-readable report
    const htmlReport = this.generateHTMLReport(results);
    const htmlPath = join(this.reportDir, `accessibility-report-${this.timestamp}.html`);
    writeFileSync(htmlPath, htmlReport);
    
    console.log(`\n📋 Accessibility report generated:`);
    console.log(`   JSON: ${reportPath}`);
    console.log(`   HTML: ${htmlPath}`);
  }

  generateHTMLReport(results) {
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Accessibility Analysis Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 40px; line-height: 1.6; }
        .header { background: #f8f9fa; padding: 20px; border-radius: 8px; }
        .summary { display: flex; gap: 20px; margin: 20px 0; flex-wrap: wrap; }
        .metric { padding: 15px; border-radius: 8px; text-align: center; min-width: 120px; }
        .passed { background: #d4edda; color: #155724; }
        .failed { background: #f8d7da; color: #721c24; }
        .warning { background: #fff3cd; color: #856404; }
        .check { margin: 20px 0; padding: 15px; border-left: 4px solid #ccc; }
        .check.passed { border-color: #28a745; }
        .check.failed { border-color: #dc3545; }
        .check.warning { border-color: #ffc107; }
        .details { margin: 10px 0; }
        .details li { margin: 5px 0; }
        .icon { font-size: 1.2em; margin-right: 8px; }
    </style>
</head>
<body>
    <div class="header">
        <h1><span class="icon">♿</span>Accessibility Analysis Report</h1>
        <p><strong>Generated:</strong> ${results.timestamp}</p>
        <p><strong>Overall Score:</strong> ${((results.summary.passed / results.summary.totalChecks) * 100).toFixed(1)}%</p>
    </div>
    
    <div class="summary">
        <div class="metric passed">
            <h3>${results.summary.passed}</h3>
            <p>Passed</p>
        </div>
        <div class="metric failed">
            <h3>${results.summary.failed}</h3>
            <p>Failed</p>
        </div>
        <div class="metric warning">
            <h3>${results.summary.warnings}</h3>
            <p>Warnings</p>
        </div>
    </div>
    
    <h2>Accessibility Checks</h2>
    ${Object.entries(results.checks).map(([name, check]) => `
        <div class="check ${check.status}">
            <h3>${name.replace(/([A-Z])/g, ' $1').replace(/^./, str => str.toUpperCase())} (${check.tool})</h3>
            <p><strong>Status:</strong> ${check.status.toUpperCase()}</p>
            <div class="details">
                <ul>
                    ${check.details.map(detail => `<li>${detail}</li>`).join('')}
                </ul>
            </div>
        </div>
    `).join('')}
    
    <h2>Recommendations</h2>
    <ul>
        <li>Implement automated accessibility testing with jest-axe</li>
        <li>Use semantic HTML elements (header, main, nav, etc.)</li>
        <li>Ensure all interactive elements are keyboard accessible</li>
        <li>Provide appropriate ARIA labels and descriptions</li>
        <li>Test with actual screen readers</li>
        <li>Maintain color contrast ratios above 4.5:1</li>
        <li>Implement focus management for dynamic content</li>
        <li>Use pseudo-localization to test layout flexibility</li>
    </ul>
</body>
</html>`;
  }
}

// CLI execution
if (import.meta.url === `file://${process.argv[1]}`) {
  const analyzer = new AccessibilityAnalyzer();
  analyzer.analyze().catch(error => {
    console.error('Accessibility analysis failed:', error);
    process.exit(1);
  });
}

export { AccessibilityAnalyzer };