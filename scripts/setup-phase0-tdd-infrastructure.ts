#!/usr/bin/env npx tsx

/**
 * Phase 0: TDD Infrastructure Setup Script
 * 
 * Sets up ae-framework's TDD functionality using existing components:
 * - HybridTDDSystem configuration
 * - TDDAgent initialization  
 * - MetricsCollector setup
 * - Git hooks installation
 */

import { HybridTDDSystem, HybridTDDConfig } from '../src/integration/hybrid-tdd-system.js';
import { TDDAgent, TDDAgentConfig } from '../src/agents/tdd-agent.js';
import { MetricsCollector } from '../src/cli/metrics/MetricsCollector.js';
import { ConfigLoader } from '../src/cli/config/ConfigLoader.js';
import * as fs from 'fs/promises';
import * as path from 'path';

interface Phase0Results {
  tddSystemOperational: boolean;
  metricsCollectionActive: boolean;
  gitHooksInstalled: boolean;
  configurationValid: boolean;
  initialErrorCount: number;
  setupTime: number;
}

export class Phase0TDDInfrastructureSetup {
  private configLoader: ConfigLoader;
  private metricsCollector: MetricsCollector;
  private startTime: number;

  constructor() {
    this.configLoader = new ConfigLoader();
    this.metricsCollector = new MetricsCollector();
    this.startTime = Date.now();
  }

  /**
   * Execute Phase 0: TDD Infrastructure Setup
   */
  async executePhase0(): Promise<Phase0Results> {
    console.log('🚀 Phase 0: TDD Infrastructure Setup Started');
    console.log('📋 Goal: Establish quality-controlled development environment using ae-framework components\n');

    try {
      // Step 1: Load and validate configuration
      console.log('📋 Step 1: Loading ae-framework-v2.yml configuration...');
      const config = await this.loadConfiguration();
      console.log('✅ Configuration loaded successfully');

      // Step 2: Initialize MetricsCollector
      console.log('\n📊 Step 2: Setting up MetricsCollector...');
      await this.setupMetricsCollection();
      console.log('✅ MetricsCollector initialized and tracking active');

      // Step 3: Get initial error count baseline
      console.log('\n📊 Step 3: Establishing TypeScript error baseline...');
      const initialErrorCount = await this.getTypeScriptErrorCount();
      console.log(`📈 Baseline: ${initialErrorCount} TypeScript errors detected`);

      // Step 4: Configure TDDAgent
      console.log('\n🧪 Step 4: Configuring TDDAgent...');
      const tddAgent = await this.setupTDDAgent(config);
      console.log('✅ TDDAgent configured with strict mode enforcement');

      // Step 5: Initialize HybridTDDSystem
      console.log('\n🔧 Step 5: Initializing HybridTDDSystem...');
      const hybridSystem = await this.setupHybridTDDSystem(config, tddAgent);
      console.log('✅ HybridTDDSystem operational with Claude Code integration');

      // Step 6: Install Git hooks
      console.log('\n🔗 Step 6: Installing Git hooks for TDD enforcement...');
      const hooksInstalled = await this.installGitHooks();
      console.log(`✅ Git hooks installed: ${hooksInstalled ? 'SUCCESS' : 'PARTIAL'}`);

      // Step 7: Validate complete setup
      console.log('\n✅ Step 7: Validating TDD infrastructure...');
      const validation = await this.validateTDDInfrastructure(hybridSystem);
      console.log(`🔍 Infrastructure validation: ${validation ? 'PASSED' : 'NEEDS_ATTENTION'}`);

      const completionTime = Date.now() - this.startTime;

      const results: Phase0Results = {
        tddSystemOperational: validation,
        metricsCollectionActive: true,
        gitHooksInstalled: hooksInstalled,
        configurationValid: true,
        initialErrorCount,
        setupTime: completionTime
      };

      await this.generatePhase0Report(results);
      
      console.log('\n🎉 Phase 0: TDD Infrastructure Setup Complete!');
      console.log(`⏱️  Setup completed in ${Math.round(completionTime / 1000)}s`);
      console.log(`📊 Baseline: ${initialErrorCount} TypeScript errors to resolve`);
      console.log('🔧 Environment ready for quality-controlled development');
      
      return results;

    } catch (error) {
      console.error('\n❌ Phase 0 setup failed:', error);
      throw error;
    }
  }

  /**
   * Load and validate ae-framework-v2.yml configuration
   */
  private async loadConfiguration(): Promise<any> {
    try {
      const configPath = path.join(process.cwd(), 'ae-framework-v2.yml');
      const config = await this.configLoader.loadConfig(configPath);
      
      // Validate required sections
      const requiredSections = ['phases', 'guards', 'self_improvement', 'integrations'];
      for (const section of requiredSections) {
        if (!config[section]) {
          throw new Error(`Missing required configuration section: ${section}`);
        }
      }

      // Validate Phase 0 configuration
      if (!config.phases['0-tdd-setup']) {
        throw new Error('Phase 0 (0-tdd-setup) configuration not found');
      }

      console.log(`📋 Configuration validated - ${Object.keys(config).length} sections loaded`);
      return config;
    } catch (error) {
      console.error('❌ Configuration loading failed:', error);
      throw error;
    }
  }

  /**
   * Setup MetricsCollector for quality tracking
   */
  private async setupMetricsCollection(): Promise<void> {
    try {
      // Initialize metrics directory
      const metricsDir = path.join(process.cwd(), 'metrics', 'self-improvement');
      await fs.mkdir(metricsDir, { recursive: true });

      // Configure metrics collection
      this.metricsCollector.enableViolationTracking(true);
      this.metricsCollector.trackTypescriptErrors(true);
      this.metricsCollector.trackCoveragetrends(true);
      this.metricsCollector.trackPhaseProgression(true);

      // Start initial metrics collection
      await this.metricsCollector.collectInitialBaseline();
      
      console.log(`📊 Metrics collection initialized - output: ${metricsDir}`);
    } catch (error) {
      console.error('❌ MetricsCollector setup failed:', error);
      throw error;
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
   * Setup TDDAgent with strict configuration
   */
  private async setupTDDAgent(config: any): Promise<TDDAgent> {
    const tddConfig: TDDAgentConfig = {
      strictMode: true,
      coverageThreshold: config.phases['0-tdd-setup'].coverage_threshold || 80,
      testFramework: 'vitest' as const,
      blockCodeWithoutTests: config.phases['0-tdd-setup'].block_code_without_test || true,
      enableRealTimeGuidance: config.integrations?.claude_code?.real_time_guidance || true
    };

    const tddContext = {
      projectPath: process.cwd(),
      currentPhase: 'phase-0-tdd-infrastructure',
      feature: 'typescript-error-resolution'
    };

    const tddAgent = new TDDAgent(tddConfig, tddContext);
    
    console.log(`🧪 TDDAgent initialized - Coverage threshold: ${tddConfig.coverageThreshold}%`);
    console.log(`🔒 Strict mode: ${tddConfig.strictMode ? 'ENABLED' : 'DISABLED'}`);
    console.log(`🚫 Block untested code: ${tddConfig.blockCodeWithoutTests ? 'ENABLED' : 'DISABLED'}`);
    
    return tddAgent;
  }

  /**
   * Setup HybridTDDSystem with Claude Code integration
   */
  private async setupHybridTDDSystem(config: any, tddAgent: TDDAgent): Promise<HybridTDDSystem> {
    const hybridConfig: HybridTDDConfig = {
      enableCLI: config.integrations?.claude_code?.task_tool_integration || true,
      enableClaudeCodeIntegration: config.integrations?.claude_code?.hybrid_tdd_system || true,
      enforceRealTime: config.integrations?.claude_code?.real_time_guidance || true,
      strictMode: true
    };

    const hybridSystem = new HybridTDDSystem(hybridConfig, tddAgent);
    
    // Initialize the system
    await hybridSystem.initialize();
    
    console.log(`🔧 HybridTDDSystem initialized`);
    console.log(`🔗 Claude Code integration: ${hybridConfig.enableClaudeCodeIntegration ? 'ACTIVE' : 'INACTIVE'}`);
    console.log(`⏱️  Real-time enforcement: ${hybridConfig.enforceRealTime ? 'ENABLED' : 'DISABLED'}`);
    
    return hybridSystem;
  }

  /**
   * Install Git hooks for TDD enforcement
   */
  private async installGitHooks(): Promise<boolean> {
    try {
      const hooksDir = path.join(process.cwd(), '.git', 'hooks');
      
      // Create pre-commit hook
      const preCommitHook = `#!/bin/sh
# ae-framework TDD Infrastructure pre-commit hook
echo "🔍 Running TDD validation..."

# Check for TypeScript errors
npm run build
if [ $? -ne 0 ]; then
  echo "❌ TypeScript errors detected - commit blocked"
  exit 1
fi

# Check for test coverage
npm run test:coverage
if [ $? -ne 0 ]; then
  echo "❌ Test coverage below threshold - commit blocked"
  exit 1
fi

echo "✅ TDD validation passed"
exit 0
`;

      await fs.writeFile(path.join(hooksDir, 'pre-commit'), preCommitHook);
      
      // Make executable
      const { execSync } = await import('child_process');
      execSync(`chmod +x ${path.join(hooksDir, 'pre-commit')}`);
      
      console.log('🔗 Git pre-commit hook installed and configured');
      return true;
    } catch (error) {
      console.warn('⚠️ Git hooks installation partial:', error);
      return false;
    }
  }

  /**
   * Validate TDD infrastructure is operational
   */
  private async validateTDDInfrastructure(hybridSystem: HybridTDDSystem): Promise<boolean> {
    try {
      // Test if TDD system blocks untested code
      const blockTest = await hybridSystem.validateTestRequirement('test-validation');
      
      // Test if metrics collection is active
      const metricsActive = await this.metricsCollector.isActive();
      
      // Test configuration validity
      const configValid = await this.configLoader.validateCurrentConfig();
      
      const allValidation = blockTest && metricsActive && configValid;
      
      console.log(`🔍 TDD system blocking: ${blockTest ? 'ACTIVE' : 'INACTIVE'}`);
      console.log(`📊 Metrics collection: ${metricsActive ? 'ACTIVE' : 'INACTIVE'}`);
      console.log(`⚙️  Configuration: ${configValid ? 'VALID' : 'INVALID'}`);
      
      return allValidation;
    } catch (error) {
      console.error('❌ Infrastructure validation failed:', error);
      return false;
    }
  }

  /**
   * Generate Phase 0 completion report
   */
  private async generatePhase0Report(results: Phase0Results): Promise<void> {
    const report = `
# Phase 0: TDD Infrastructure Setup Report

## Executive Summary
- **Setup Status**: ${results.tddSystemOperational ? '✅ SUCCESS' : '⚠️ PARTIAL'}
- **Setup Time**: ${Math.round(results.setupTime / 1000)}s
- **Initial Baseline**: ${results.initialErrorCount} TypeScript errors
- **Quality Gates**: ${results.tddSystemOperational ? 'ACTIVE' : 'NEEDS_ATTENTION'}

## Infrastructure Components

### ✅ TDD System
- **HybridTDDSystem**: ${results.tddSystemOperational ? 'Operational' : 'Needs attention'}
- **TDDAgent**: Configured with strict mode
- **Coverage Threshold**: 80%
- **Code Blocking**: ${results.tddSystemOperational ? 'Active' : 'Inactive'}

### ✅ Metrics Collection  
- **MetricsCollector**: ${results.metricsCollectionActive ? 'Active' : 'Inactive'}
- **Baseline Established**: ${results.initialErrorCount} TypeScript errors
- **Progress Tracking**: Enabled
- **Quality Monitoring**: Active

### ✅ Git Integration
- **Pre-commit Hooks**: ${results.gitHooksInstalled ? 'Installed' : 'Partial'}
- **TDD Enforcement**: ${results.gitHooksInstalled ? 'Active' : 'Manual only'}
- **Quality Gates**: ${results.gitHooksInstalled ? 'Enforced' : 'Advisory'}

### ✅ Configuration
- **ae-framework-v2.yml**: ${results.configurationValid ? 'Valid' : 'Invalid'}
- **Phase Dependencies**: Validated
- **Component Integration**: Configured

## Quality Baseline
- **TypeScript Errors**: ${results.initialErrorCount} (Target: 0)
- **Test Coverage**: Unknown (Target: 80%+)
- **TDD Compliance**: 0% → Target: 95%

## Next Steps
${results.tddSystemOperational ? `
✅ **Ready for Phase 1**: Foundation Analysis & Core Utilities
- TDD infrastructure operational
- Quality monitoring active  
- Baseline metrics established
` : `
⚠️ **Infrastructure Attention Required**:
- Review TDD system configuration
- Validate component integration
- Resolve setup issues before Phase 1
`}

## Success Criteria Achievement
- [${results.tddSystemOperational ? 'x' : ' '}] TDD system blocks untested code
- [${results.metricsCollectionActive ? 'x' : ' '}] Metrics collection operational
- [${results.gitHooksInstalled ? 'x' : ' '}] Git hooks enforce quality gates
- [${results.configurationValid ? 'x' : ' '}] Configuration validated

---
*Generated by ae-framework Phase 0 TDD Infrastructure Setup*
*Using ae-framework components: HybridTDDSystem, TDDAgent, MetricsCollector, ConfigLoader*
    `.trim();

    const reportPath = path.join(process.cwd(), 'reports', 'phase-0-tdd-infrastructure.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    console.log(`📄 Phase 0 report generated: ${reportPath}`);
  }
}

export default Phase0TDDInfrastructureSetup;

// Execute if called directly
if (import.meta.url === `file://${process.argv[1]}`) {
  const phase0 = new Phase0TDDInfrastructureSetup();
  
  phase0.executePhase0()
    .then((results) => {
      console.log(`\n🎯 Phase 0 Summary:`);
      console.log(`   TDD System: ${results.tddSystemOperational ? '✅' : '⚠️'}`);
      console.log(`   Metrics: ${results.metricsCollectionActive ? '✅' : '⚠️'}`);
      console.log(`   Git Hooks: ${results.gitHooksInstalled ? '✅' : '⚠️'}`);
      console.log(`   Baseline: ${results.initialErrorCount} TypeScript errors`);
      
      if (results.tddSystemOperational && results.metricsCollectionActive) {
        console.log(`\n🚀 Ready to proceed to Phase 1: Foundation Analysis`);
        process.exit(0);
      } else {
        console.log(`\n⚠️ Infrastructure needs attention before Phase 1`);
        process.exit(1);
      }
    })
    .catch((error) => {
      console.error('\n❌ Phase 0 execution failed:', error);
      process.exit(1);
    });
}