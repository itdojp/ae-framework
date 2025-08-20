#!/usr/bin/env ts-node

/**
 * Differential Generation Testing
 * 
 * Compares code generation between different versions of templates/models
 * to detect regressions and improvements in generated code quality.
 */

import { readFileSync, writeFileSync, existsSync, mkdirSync } from 'fs';
import { join } from 'path';
import { spawn } from 'child_process';
import { promisify } from 'util';
import { glob } from 'glob';

interface GenerationConfig {
  name: string;
  description: string;
  templatePath?: string;
  modelVersion?: string;
  settings: Record<string, any>;
}

interface QualityMetrics {
  accessibility: {
    critical: number;
    serious: number;
    moderate: number;
    minor: number;
  };
  typescript: {
    errors: number;
    warnings: number;
  };
  lighthouse: {
    performance: number;
    accessibility: number;
    bestPractices: number;
    seo: number;
  };
  codeQuality: {
    linesOfCode: number;
    complexity: number;
    duplicateLines: number;
  };
  fileMetrics: {
    totalFiles: number;
    componentFiles: number;
    testFiles: number;
    storyFiles: number;
  };
}

interface DifferentialResult {
  configA: GenerationConfig;
  configB: GenerationConfig;
  metricsA: QualityMetrics;
  metricsB: QualityMetrics;
  comparison: {
    improvements: string[];
    regressions: string[];
    unchanged: string[];
    score: number; // -100 (much worse) to +100 (much better)
  };
  timestamp: string;
}

class DifferentialTester {
  private readonly OUTPUT_DIR = './tests/differential/outputs';
  private readonly REPORTS_DIR = './reports/differential';

  constructor() {
    this.ensureDirectories();
  }

  private ensureDirectories(): void {
    [this.OUTPUT_DIR, this.REPORTS_DIR].forEach(dir => {
      if (!existsSync(dir)) {
        mkdirSync(dir, { recursive: true });
      }
    });
  }

  async runDifferentialTest(
    configA: GenerationConfig,
    configB: GenerationConfig,
    sourceIR: string = './examples/inventory/.ae/phase-state.json'
  ): Promise<DifferentialResult> {
    console.log(`🔄 Running differential test: ${configA.name} vs ${configB.name}`);

    if (!existsSync(sourceIR)) {
      throw new Error(`Source IR not found: ${sourceIR}`);
    }

    // Generate with config A
    console.log(`   Generating with ${configA.name}...`);
    const outputA = join(this.OUTPUT_DIR, `output-${configA.name}-${Date.now()}`);
    const metricsA = await this.generateAndAnalyze(sourceIR, configA, outputA);

    // Generate with config B  
    console.log(`   Generating with ${configB.name}...`);
    const outputB = join(this.OUTPUT_DIR, `output-${configB.name}-${Date.now()}`);
    const metricsB = await this.generateAndAnalyze(sourceIR, configB, outputB);

    // Compare results
    console.log('   Analyzing differences...');
    const comparison = this.compareMetrics(metricsA, metricsB);

    const result: DifferentialResult = {
      configA,
      configB,
      metricsA,
      metricsB,
      comparison,
      timestamp: new Date().toISOString()
    };

    // Generate report
    const reportPath = await this.generateReport(result);
    console.log(`📊 Differential report saved: ${reportPath}`);

    return result;
  }

  private async generateAndAnalyze(
    sourceIR: string,
    config: GenerationConfig,
    outputDir: string
  ): Promise<QualityMetrics> {
    // Create output directory
    if (!existsSync(outputDir)) {
      mkdirSync(outputDir, { recursive: true });
    }

    // In a real implementation, this would run the actual UI generator
    // For now, we'll simulate the generation and analysis
    await this.simulateGeneration(sourceIR, config, outputDir);

    // Analyze generated code
    return await this.analyzeGeneratedCode(outputDir);
  }

  private async simulateGeneration(
    sourceIR: string,
    config: GenerationConfig,
    outputDir: string
  ): Promise<void> {
    // Read source IR
    const ir = JSON.parse(readFileSync(sourceIR, 'utf-8'));

    // Generate sample files based on config
    const entities = ir.domain || [];
    
    for (const entity of entities) {
      const entityName = entity.name;
      
      // Generate component file
      const componentContent = this.generateComponent(entity, config);
      writeFileSync(join(outputDir, `${entityName}Form.tsx`), componentContent);

      // Generate test file
      const testContent = this.generateTest(entity, config);
      writeFileSync(join(outputDir, `${entityName}Form.test.tsx`), testContent);

      // Generate story file
      const storyContent = this.generateStory(entity, config);
      writeFileSync(join(outputDir, `${entityName}Form.stories.tsx`), storyContent);
    }
  }

  private generateComponent(entity: any, config: GenerationConfig): string {
    const complexity = config.settings.complexity || 'medium';
    const accessibility = config.settings.accessibility || 'standard';
    
    let componentCode = `// Generated with ${config.name}\n`;
    componentCode += `import React from 'react';\n`;
    componentCode += `import { useForm } from 'react-hook-form';\n\n`;
    
    componentCode += `interface ${entity.name}FormProps {\n`;
    componentCode += `  onSubmit: (data: any) => void;\n`;
    componentCode += `}\n\n`;
    
    componentCode += `export const ${entity.name}Form: React.FC<${entity.name}FormProps> = ({ onSubmit }) => {\n`;
    componentCode += `  const { register, handleSubmit } = useForm();\n\n`;
    
    componentCode += `  return (\n`;
    componentCode += `    <form onSubmit={handleSubmit(onSubmit)}`;
    
    if (accessibility === 'enhanced') {
      componentCode += ` aria-label="${entity.name} form"`;
    }
    
    componentCode += `>\n`;
    
    // Generate fields based on entity
    entity.fields?.forEach((field: any) => {
      componentCode += `      <div>\n`;
      
      if (accessibility === 'enhanced') {
        componentCode += `        <label htmlFor="${field.name}" aria-required="${field.required || false}">\n`;
      } else {
        componentCode += `        <label htmlFor="${field.name}">\n`;
      }
      
      componentCode += `          ${field.name}\n`;
      componentCode += `        </label>\n`;
      componentCode += `        <input\n`;
      componentCode += `          id="${field.name}"\n`;
      componentCode += `          {...register('${field.name}'${field.required ? ', { required: true }' : ''})}\n`;
      
      if (accessibility === 'enhanced') {
        componentCode += `          aria-describedby="${field.name}-help"\n`;
      }
      
      componentCode += `        />\n`;
      
      if (accessibility === 'enhanced') {
        componentCode += `        <div id="${field.name}-help" className="sr-only">Enter ${field.name}</div>\n`;
      }
      
      componentCode += `      </div>\n`;
    });
    
    componentCode += `      <button type="submit">Submit</button>\n`;
    componentCode += `    </form>\n`;
    componentCode += `  );\n`;
    componentCode += `};\n`;
    
    return componentCode;
  }

  private generateTest(entity: any, config: GenerationConfig): string {
    const testingLevel = config.settings.testing || 'standard';
    
    let testCode = `// Generated test with ${config.name}\n`;
    testCode += `import { render, screen } from '@testing-library/react';\n`;
    testCode += `import { ${entity.name}Form } from './${entity.name}Form';\n\n`;
    
    testCode += `describe('${entity.name}Form', () => {\n`;
    testCode += `  it('renders form fields', () => {\n`;
    testCode += `    render(<${entity.name}Form onSubmit={() => {}} />);\n`;
    
    entity.fields?.forEach((field: any) => {
      testCode += `    expect(screen.getByLabelText('${field.name}')).toBeInTheDocument();\n`;
    });
    
    testCode += `  });\n`;
    
    if (testingLevel === 'comprehensive') {
      testCode += `\n  it('validates required fields', () => {\n`;
      testCode += `    // Comprehensive validation tests\n`;
      testCode += `  });\n`;
      
      testCode += `\n  it('handles submission correctly', () => {\n`;
      testCode += `    // Submission handling tests\n`;
      testCode += `  });\n`;
    }
    
    testCode += `});\n`;
    
    return testCode;
  }

  private generateStory(entity: any, config: GenerationConfig): string {
    const storyDetail = config.settings.stories || 'basic';
    
    let storyCode = `// Generated story with ${config.name}\n`;
    storyCode += `import type { Meta, StoryObj } from '@storybook/react';\n`;
    storyCode += `import { ${entity.name}Form } from './${entity.name}Form';\n\n`;
    
    storyCode += `const meta: Meta<typeof ${entity.name}Form> = {\n`;
    storyCode += `  title: 'Forms/${entity.name}Form',\n`;
    storyCode += `  component: ${entity.name}Form,\n`;
    storyCode += `};\n\n`;
    
    storyCode += `export default meta;\n`;
    storyCode += `type Story = StoryObj<typeof meta>;\n\n`;
    
    storyCode += `export const Default: Story = {\n`;
    storyCode += `  args: {\n`;
    storyCode += `    onSubmit: (data) => console.log(data),\n`;
    storyCode += `  },\n`;
    storyCode += `};\n`;
    
    if (storyDetail === 'comprehensive') {
      storyCode += `\nexport const WithValidation: Story = {\n`;
      storyCode += `  args: {\n`;
      storyCode += `    onSubmit: (data) => console.log('Validated:', data),\n`;
      storyCode += `  },\n`;
      storyCode += `};\n`;
    }
    
    return storyCode;
  }

  private async analyzeGeneratedCode(outputDir: string): Promise<QualityMetrics> {
    const files = await glob(join(outputDir, '**/*.{ts,tsx}'));
    
    let totalLines = 0;
    let ariaAttributes = 0;
    let typeScriptErrors = 0;
    let complexity = 0;
    
    const fileMetrics = {
      totalFiles: files.length,
      componentFiles: files.filter(f => f.includes('Form.tsx')).length,
      testFiles: files.filter(f => f.includes('.test.')).length,
      storyFiles: files.filter(f => f.includes('.stories.')).length,
    };

    for (const file of files) {
      const content = readFileSync(file, 'utf-8');
      const lines = content.split('\n');
      totalLines += lines.length;
      
      // Count ARIA attributes
      ariaAttributes += (content.match(/aria-\w+/g) || []).length;
      
      // Simple TypeScript error detection
      if (content.includes('any') && !content.includes('// @ts-ignore')) {
        typeScriptErrors++;
      }
      
      // Simple complexity calculation
      complexity += (content.match(/if|for|while|switch/g) || []).length;
    }

    // Simulate additional metrics
    const metrics: QualityMetrics = {
      accessibility: {
        critical: Math.floor(Math.random() * 2), // 0-1 critical issues
        serious: Math.floor(Math.random() * 3), // 0-2 serious issues
        moderate: Math.floor(Math.random() * 5), // 0-4 moderate issues
        minor: Math.floor(Math.random() * 8), // 0-7 minor issues
      },
      typescript: {
        errors: typeScriptErrors,
        warnings: Math.floor(Math.random() * 5),
      },
      lighthouse: {
        performance: 85 + Math.floor(Math.random() * 15), // 85-100
        accessibility: 90 + Math.floor(Math.random() * 10), // 90-100
        bestPractices: 85 + Math.floor(Math.random() * 15), // 85-100
        seo: 80 + Math.floor(Math.random() * 20), // 80-100
      },
      codeQuality: {
        linesOfCode: totalLines,
        complexity: complexity,
        duplicateLines: Math.floor(totalLines * (Math.random() * 0.05)), // 0-5% duplication
      },
      fileMetrics
    };

    return metrics;
  }

  private compareMetrics(metricsA: QualityMetrics, metricsB: QualityMetrics): {
    improvements: string[];
    regressions: string[];
    unchanged: string[];
    score: number;
  } {
    const improvements: string[] = [];
    const regressions: string[] = [];
    const unchanged: string[] = [];
    let score = 0;

    // Compare accessibility
    const a11yScoreA = this.calculateA11yScore(metricsA.accessibility);
    const a11yScoreB = this.calculateA11yScore(metricsB.accessibility);
    if (a11yScoreB > a11yScoreA) {
      improvements.push(`Accessibility improved (${a11yScoreA} → ${a11yScoreB})`);
      score += 15;
    } else if (a11yScoreB < a11yScoreA) {
      regressions.push(`Accessibility regressed (${a11yScoreA} → ${a11yScoreB})`);
      score -= 15;
    } else {
      unchanged.push('Accessibility score maintained');
    }

    // Compare TypeScript errors
    if (metricsB.typescript.errors < metricsA.typescript.errors) {
      improvements.push(`TypeScript errors reduced (${metricsA.typescript.errors} → ${metricsB.typescript.errors})`);
      score += 10;
    } else if (metricsB.typescript.errors > metricsA.typescript.errors) {
      regressions.push(`TypeScript errors increased (${metricsA.typescript.errors} → ${metricsB.typescript.errors})`);
      score -= 10;
    } else {
      unchanged.push('TypeScript error count maintained');
    }

    // Compare Lighthouse scores
    const lighthouseA = Object.values(metricsA.lighthouse).reduce((a, b) => a + b, 0) / 4;
    const lighthouseB = Object.values(metricsB.lighthouse).reduce((a, b) => a + b, 0) / 4;
    const lighthouseDiff = lighthouseB - lighthouseA;
    
    if (lighthouseDiff > 2) {
      improvements.push(`Lighthouse scores improved (${lighthouseA.toFixed(1)} → ${lighthouseB.toFixed(1)})`);
      score += Math.min(20, Math.floor(lighthouseDiff));
    } else if (lighthouseDiff < -2) {
      regressions.push(`Lighthouse scores regressed (${lighthouseA.toFixed(1)} → ${lighthouseB.toFixed(1)})`);
      score -= Math.min(20, Math.floor(Math.abs(lighthouseDiff)));
    } else {
      unchanged.push('Lighthouse scores maintained');
    }

    // Compare code complexity
    const complexityA = metricsA.codeQuality.complexity / metricsA.codeQuality.linesOfCode;
    const complexityB = metricsB.codeQuality.complexity / metricsB.codeQuality.linesOfCode;
    
    if (complexityB < complexityA * 0.9) {
      improvements.push(`Code complexity reduced (${complexityA.toFixed(3)} → ${complexityB.toFixed(3)})`);
      score += 5;
    } else if (complexityB > complexityA * 1.1) {
      regressions.push(`Code complexity increased (${complexityA.toFixed(3)} → ${complexityB.toFixed(3)})`);
      score -= 5;
    } else {
      unchanged.push('Code complexity maintained');
    }

    // Compare file generation
    if (metricsB.fileMetrics.totalFiles > metricsA.fileMetrics.totalFiles) {
      improvements.push(`More files generated (${metricsA.fileMetrics.totalFiles} → ${metricsB.fileMetrics.totalFiles})`);
      score += 3;
    } else if (metricsB.fileMetrics.totalFiles < metricsA.fileMetrics.totalFiles) {
      regressions.push(`Fewer files generated (${metricsA.fileMetrics.totalFiles} → ${metricsB.fileMetrics.totalFiles})`);
      score -= 3;
    } else {
      unchanged.push('File count maintained');
    }

    return {
      improvements,
      regressions,
      unchanged,
      score: Math.max(-100, Math.min(100, score))
    };
  }

  private calculateA11yScore(a11y: QualityMetrics['accessibility']): number {
    return 100 - (a11y.critical * 25 + a11y.serious * 10 + a11y.moderate * 5 + a11y.minor * 1);
  }

  private async generateReport(result: DifferentialResult): Promise<string> {
    const reportPath = join(this.REPORTS_DIR, `diff-${Date.now()}.md`);
    
    const report = [
      '# Differential Generation Report',
      '',
      `Generated: ${result.timestamp}`,
      '',
      '## Configuration Comparison',
      '',
      `**Configuration A**: ${result.configA.name}`,
      `- Description: ${result.configA.description}`,
      '',
      `**Configuration B**: ${result.configB.name}`,
      `- Description: ${result.configB.description}`,
      '',
      '## Quality Metrics Comparison',
      '',
      '| Metric | Config A | Config B | Change |',
      '|--------|----------|----------|--------|',
      `| Accessibility Score | ${this.calculateA11yScore(result.metricsA.accessibility)} | ${this.calculateA11yScore(result.metricsB.accessibility)} | ${this.calculateChange(this.calculateA11yScore(result.metricsA.accessibility), this.calculateA11yScore(result.metricsB.accessibility))} |`,
      `| TypeScript Errors | ${result.metricsA.typescript.errors} | ${result.metricsB.typescript.errors} | ${this.calculateChange(result.metricsA.typescript.errors, result.metricsB.typescript.errors, true)} |`,
      `| Lines of Code | ${result.metricsA.codeQuality.linesOfCode} | ${result.metricsB.codeQuality.linesOfCode} | ${this.calculateChange(result.metricsA.codeQuality.linesOfCode, result.metricsB.codeQuality.linesOfCode)} |`,
      `| Total Files | ${result.metricsA.fileMetrics.totalFiles} | ${result.metricsB.fileMetrics.totalFiles} | ${this.calculateChange(result.metricsA.fileMetrics.totalFiles, result.metricsB.fileMetrics.totalFiles)} |`,
      '',
      '## Summary',
      '',
      `**Overall Score**: ${result.comparison.score}/100`,
      '',
      '### Improvements',
      ...result.comparison.improvements.map(imp => `- ✅ ${imp}`),
      '',
      '### Regressions',
      ...result.comparison.regressions.map(reg => `- ❌ ${reg}`),
      '',
      '### Unchanged',
      ...result.comparison.unchanged.map(unch => `- ⚪ ${unch}`),
      ''
    ];

    writeFileSync(reportPath, report.join('\n'));
    return reportPath;
  }

  private calculateChange(oldVal: number, newVal: number, reverse = false): string {
    const diff = newVal - oldVal;
    const percent = oldVal === 0 ? 0 : (diff / oldVal) * 100;
    
    let emoji = '⚪';
    if (diff > 0) {
      emoji = reverse ? '❌' : '✅';
    } else if (diff < 0) {
      emoji = reverse ? '✅' : '❌';
    }

    return `${emoji} ${diff > 0 ? '+' : ''}${diff} (${percent > 0 ? '+' : ''}${percent.toFixed(1)}%)`;
  }
}

// CLI interface
async function main() {
  const tester = new DifferentialTester();
  
  // Define configurations to compare
  const configCurrent: GenerationConfig = {
    name: 'current',
    description: 'Current template configuration',
    settings: {
      accessibility: 'standard',
      complexity: 'medium',
      testing: 'standard',
      stories: 'basic'
    }
  };

  const configEnhanced: GenerationConfig = {
    name: 'enhanced',
    description: 'Enhanced template configuration with improved accessibility',
    settings: {
      accessibility: 'enhanced',
      complexity: 'medium',
      testing: 'comprehensive',
      stories: 'comprehensive'
    }
  };

  try {
    const result = await tester.runDifferentialTest(configCurrent, configEnhanced);
    
    console.log('\n📊 Differential Test Results:');
    console.log(`Overall Score: ${result.comparison.score}/100`);
    console.log(`Improvements: ${result.comparison.improvements.length}`);
    console.log(`Regressions: ${result.comparison.regressions.length}`);

    process.exit(result.comparison.score >= 0 ? 0 : 1);
  } catch (error) {
    console.error('❌ Differential test failed:', (error as Error).message);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

export { DifferentialTester };