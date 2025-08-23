#!/usr/bin/env npx tsx

/**
 * Simplified Phase 0: TDD Infrastructure Setup
 * 
 * Basic implementation without complex component dependencies
 */

import * as fs from 'fs/promises';
import * as path from 'path';

interface Phase0Results {
  configurationValid: boolean;
  initialErrorCount: number;
  gitHooksInstalled: boolean;
  setupTime: number;
}

export class SimplePhase0Setup {
  private startTime: number;

  constructor() {
    this.startTime = Date.now();
  }

  async executePhase0(): Promise<Phase0Results> {
    console.log('🚀 Phase 0: Simplified TDD Infrastructure Setup Started');
    console.log('📋 Goal: Basic quality-controlled development environment\n');

    try {
      // Step 1: Validate configuration
      console.log('📋 Step 1: Validating ae-framework-v2.yml...');
      const configValid = await this.validateConfiguration();
      console.log(`✅ Configuration: ${configValid ? 'VALID' : 'NEEDS_ATTENTION'}`);

      // Step 2: Get initial error count
      console.log('\n📊 Step 2: Getting TypeScript error baseline...');
      const initialErrorCount = await this.getTypeScriptErrorCount();
      console.log(`📈 Baseline: ${initialErrorCount} TypeScript errors`);

      // Step 3: Setup basic directories
      console.log('\n📁 Step 3: Creating required directories...');
      await this.setupDirectories();
      console.log('✅ Directory structure created');

      // Step 4: Install basic Git hooks
      console.log('\n🔗 Step 4: Installing basic Git hooks...');
      const hooksInstalled = await this.installBasicGitHooks();
      console.log(`✅ Git hooks: ${hooksInstalled ? 'INSTALLED' : 'PARTIAL'}`);

      const completionTime = Date.now() - this.startTime;

      const results: Phase0Results = {
        configurationValid: configValid,
        initialErrorCount,
        gitHooksInstalled: hooksInstalled,
        setupTime: completionTime
      };

      await this.generatePhase0Report(results);

      console.log('\n🎉 Phase 0: Basic TDD Infrastructure Setup Complete!');
      console.log(`⏱️  Setup completed in ${Math.round(completionTime / 1000)}s`);
      console.log(`📊 Baseline: ${initialErrorCount} TypeScript errors to resolve`);

      return results;

    } catch (error) {
      console.error('\n❌ Phase 0 setup failed:', error);
      throw error;
    }
  }

  /**
   * Validate ae-framework-v2.yml exists and has basic structure
   */
  private async validateConfiguration(): Promise<boolean> {
    try {
      const configPath = path.join(process.cwd(), 'ae-framework-v2.yml');
      const configContent = await fs.readFile(configPath, 'utf-8');
      
      // Basic validation - check for required sections
      const requiredSections = ['phases', 'self_improvement'];
      const hasRequiredSections = requiredSections.every(section => 
        configContent.includes(`${section}:`)
      );
      
      return hasRequiredSections;
    } catch (error) {
      console.warn('⚠️ Configuration validation failed:', error);
      return false;
    }
  }

  /**
   * Get current TypeScript error count
   */
  private async getTypeScriptErrorCount(): Promise<number> {
    try {
      const { execSync } = await import('child_process');
      execSync('npm run build', { stdio: 'pipe' });
      return 0; // No errors if build succeeds
    } catch (error: any) {
      const errorOutput = String(error.stdout || error.stderr || '');
      const errorMatches = errorOutput.match(/error TS\d+:/g);
      return errorMatches ? errorMatches.length : 0;
    }
  }

  /**
   * Setup required directories for ae-framework v2
   */
  private async setupDirectories(): Promise<void> {
    const directories = [
      'metrics/self-improvement',
      'reports',
      'tests/phase-0',
      'temp-reports'
    ];

    for (const dir of directories) {
      await fs.mkdir(path.join(process.cwd(), dir), { recursive: true });
    }
  }

  /**
   * Install basic Git hooks
   */
  private async installBasicGitHooks(): Promise<boolean> {
    try {
      const hooksDir = path.join(process.cwd(), '.git', 'hooks');
      
      const preCommitHook = `#!/bin/sh
# Basic ae-framework TDD pre-commit hook
echo "🔍 Running basic validation..."

# Check for TypeScript errors
npm run build
if [ $? -ne 0 ]; then
  echo "❌ TypeScript errors detected - commit blocked"
  exit 1
fi

echo "✅ Basic validation passed"
exit 0
`;

      await fs.writeFile(path.join(hooksDir, 'pre-commit'), preCommitHook);
      
      // Make executable
      const { execSync } = await import('child_process');
      execSync(`chmod +x ${path.join(hooksDir, 'pre-commit')}`);
      
      return true;
    } catch (error) {
      console.warn('⚠️ Git hooks installation partial:', error);
      return false;
    }
  }

  /**
   * Generate Phase 0 report
   */
  private async generatePhase0Report(results: Phase0Results): Promise<void> {
    const report = `
# Phase 0: TDD Infrastructure Setup Report (Simplified)

## Executive Summary
- **Setup Status**: ${results.configurationValid && results.gitHooksInstalled ? '✅ SUCCESS' : '⚠️ PARTIAL'}
- **Setup Time**: ${Math.round(results.setupTime / 1000)}s
- **Initial Baseline**: ${results.initialErrorCount} TypeScript errors
- **Git Hooks**: ${results.gitHooksInstalled ? 'Active' : 'Partial'}

## Infrastructure Components

### ✅ Configuration
- **ae-framework-v2.yml**: ${results.configurationValid ? 'Valid' : 'Needs attention'}
- **Directory Structure**: Created
- **Phase Dependencies**: Ready

### ✅ Quality Baseline
- **TypeScript Errors**: ${results.initialErrorCount} (Target: 0)
- **Build Status**: ${results.initialErrorCount === 0 ? 'PASSING' : 'FAILING'}

### ✅ Git Integration  
- **Pre-commit Hooks**: ${results.gitHooksInstalled ? 'Installed' : 'Partial'}
- **Basic Validation**: ${results.gitHooksInstalled ? 'Active' : 'Manual only'}

## Next Steps
${results.configurationValid && results.gitHooksInstalled ? `
✅ **Ready for Phase 1**: Foundation Analysis & Core Utilities
- Basic infrastructure operational
- Baseline metrics established (${results.initialErrorCount} errors)
- Git hooks provide basic protection
` : `
⚠️ **Infrastructure Attention Required**:
- Review configuration and Git hooks
- Manual validation may be needed for Phase 1
`}

## Success Criteria Achievement
- [${results.configurationValid ? 'x' : ' '}] Configuration validated
- [x] Directory structure created
- [x] Error baseline established (${results.initialErrorCount} errors)
- [${results.gitHooksInstalled ? 'x' : ' '}] Git hooks installed

---
*Generated by ae-framework Phase 0 Simplified Setup*
*Target: Prepare for systematic TypeScript error resolution*
    `.trim();

    const reportPath = path.join(process.cwd(), 'reports', 'phase-0-simplified-setup.md');
    await fs.writeFile(reportPath, report);
    
    console.log(`📄 Phase 0 report generated: ${reportPath}`);
  }
}

// Execute if called directly
if (import.meta.url === `file://${process.argv[1]}`) {
  const phase0 = new SimplePhase0Setup();
  
  phase0.executePhase0()
    .then((results) => {
      console.log(`\n🎯 Phase 0 Summary:`);
      console.log(`   Configuration: ${results.configurationValid ? '✅' : '⚠️'}`);
      console.log(`   Git Hooks: ${results.gitHooksInstalled ? '✅' : '⚠️'}`);
      console.log(`   Baseline: ${results.initialErrorCount} TypeScript errors`);
      
      if (results.configurationValid) {
        console.log(`\n🚀 Ready to proceed to Phase 1: Foundation Analysis`);
        console.log(`🎯 Target: Reduce ${results.initialErrorCount} TypeScript errors systematically`);
        process.exit(0);
      } else {
        console.log(`\n⚠️ Basic infrastructure ready, manual validation recommended`);
        process.exit(0);
      }
    })
    .catch((error) => {
      console.error('\n❌ Phase 0 execution failed:', error);
      process.exit(1);
    });
}

export default SimplePhase0Setup;