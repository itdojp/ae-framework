/**
 * TDD Infrastructure Setup for ae-framework Self-Improvement
 * 
 * This module configures and initializes the TDD infrastructure using
 * ae-framework's existing components for quality-controlled reimplementation.
 */

import { HybridTDDSystem, type HybridTDDConfig } from '../integration/hybrid-tdd-system.js';
import { TDDAgent, type TDDAgentConfig } from '../agents/tdd-agent.js';
import { MetricsCollector } from '../cli/metrics/MetricsCollector.js';
import { ConfigLoader } from '../cli/config/ConfigLoader.js';
import * as fs from 'node:fs';
import * as path from 'node:path';

export interface SelfImprovementTDDConfig {
  projectRoot: string;
  configFile: string;
  enableRealTimeMonitoring: boolean;
  strictModeEnforcement: boolean;
  targetCoverage: number;
  metricsOutputPath: string;
}

export class SelfImprovementTDDSetup {
  private hybridTDD?: HybridTDDSystem;
  private tddAgent?: TDDAgent;
  private metricsCollector?: MetricsCollector;
  private config: SelfImprovementTDDConfig;

  constructor(config: Partial<SelfImprovementTDDConfig> = {}) {
    this.config = {
      projectRoot: process.cwd(),
      configFile: 'ae-framework-v2.yml',
      enableRealTimeMonitoring: true,
      strictModeEnforcement: true,
      targetCoverage: 80,
      metricsOutputPath: 'metrics/self-improvement',
      ...config
    };
  }

  /**
   * Initialize TDD infrastructure for self-improvement project
   */
  async initializeTDDInfrastructure(): Promise<{
    success: boolean;
    components: {
      hybridTDD: boolean;
      tddAgent: boolean;
      metricsCollector: boolean;
    };
    message: string;
  }> {
    try {
      console.log('🚀 Initializing ae-framework Self-Improvement TDD Infrastructure...');

      // 1. Load ae-framework-v2.yml configuration
      const aeConfig = this.loadSelfImprovementConfig();
      
      // 2. Set up HybridTDDSystem
      const hybridTDDResult = await this.setupHybridTDDSystem(aeConfig);
      
      // 3. Configure TDDAgent
      const tddAgentResult = await this.setupTDDAgent();
      
      // 4. Initialize MetricsCollector
      const metricsResult = await this.setupMetricsCollector(aeConfig);

      // 5. Start proactive monitoring
      if (this.config.enableRealTimeMonitoring && this.hybridTDD) {
        await this.hybridTDD.startProactiveMonitoring();
      }

      const success = hybridTDDResult && tddAgentResult && metricsResult;
      
      return {
        success,
        components: {
          hybridTDD: hybridTDDResult,
          tddAgent: tddAgentResult,
          metricsCollector: metricsResult
        },
        message: success 
          ? '✅ TDD Infrastructure successfully initialized for self-improvement'
          : '❌ TDD Infrastructure setup failed - check component status'
      };

    } catch (error) {
      console.error('❌ Failed to initialize TDD infrastructure:', error);
      return {
        success: false,
        components: {
          hybridTDD: false,
          tddAgent: false,
          metricsCollector: false
        },
        message: `Failed to initialize TDD infrastructure: ${error instanceof Error ? error.message : error}`
      };
    }
  }

  /**
   * Load self-improvement configuration
   */
  private loadSelfImprovementConfig() {
    const configPath = path.join(this.config.projectRoot, this.config.configFile);
    
    if (!fs.existsSync(configPath)) {
      throw new Error(`Configuration file not found: ${configPath}`);
    }

    // Use ConfigLoader to load and validate configuration
    const config = ConfigLoader.load(configPath);
    console.log(`📋 Loaded configuration: ${config.name} v${config.version}`);
    
    return config;
  }

  /**
   * Set up HybridTDDSystem for Claude Code integration
   */
  private async setupHybridTDDSystem(aeConfig: any): Promise<boolean> {
    try {
      const hybridConfig: HybridTDDConfig = {
        enableCLI: true,
        enableMCPServer: false, // Focus on Claude Code integration
        enableClaudeCodeIntegration: true,
        enforceRealTime: this.config.enableRealTimeMonitoring,
        strictMode: this.config.strictModeEnforcement,
        enableSpecSSot: true,
        specPath: 'spec/ae-framework-v2-spec.md',
        aeIrOutputPath: '.ae/self-improvement-ir.json'
      };

      this.hybridTDD = new HybridTDDSystem(hybridConfig);
      console.log('✅ HybridTDDSystem configured for Claude Code integration');
      return true;

    } catch (error) {
      console.error('❌ Failed to setup HybridTDDSystem:', error);
      return false;
    }
  }

  /**
   * Configure TDDAgent for real-time enforcement
   */
  private async setupTDDAgent(): Promise<boolean> {
    try {
      const agentConfig: TDDAgentConfig = {
        strictMode: this.config.strictModeEnforcement,
        coverageThreshold: this.config.targetCoverage,
        testFramework: 'vitest',
        blockCodeWithoutTests: true,
        enableRealTimeGuidance: this.config.enableRealTimeMonitoring
      };

      const tddContext = {
        projectPath: this.config.projectRoot,
        currentPhase: '0-tdd-setup',
        feature: 'ae-framework-self-improvement',
        lastAction: 'tdd-infrastructure-setup'
      };

      this.tddAgent = new TDDAgent(agentConfig, tddContext);
      console.log('✅ TDDAgent configured for real-time enforcement');
      return true;

    } catch (error) {
      console.error('❌ Failed to setup TDDAgent:', error);
      return false;
    }
  }

  /**
   * Initialize MetricsCollector for progress tracking
   */
  private async setupMetricsCollector(aeConfig: any): Promise<boolean> {
    try {
      // Ensure metrics directory exists
      const metricsDir = path.join(this.config.projectRoot, this.config.metricsOutputPath);
      if (!fs.existsSync(metricsDir)) {
        fs.mkdirSync(metricsDir, { recursive: true });
      }

      this.metricsCollector = new MetricsCollector(aeConfig);
      
      // Start tracking self-improvement project
      this.metricsCollector.startPhase('0-tdd-setup');
      
      // Record initial baseline
      this.metricsCollector.recordArtifact('ae-framework-v2.yml');
      
      console.log('✅ MetricsCollector initialized for self-improvement tracking');
      return true;

    } catch (error) {
      console.error('❌ Failed to setup MetricsCollector:', error);
      return false;
    }
  }

  /**
   * Validate TDD infrastructure is operational
   */
  async validateTDDInfrastructure(): Promise<{
    operational: boolean;
    checks: {
      hybridTDDActive: boolean;
      tddAgentReady: boolean;
      metricsCollecting: boolean;
      configValid: boolean;
    };
    recommendations: string[];
  }> {
    const checks = {
      hybridTDDActive: !!this.hybridTDD,
      tddAgentReady: !!this.tddAgent,
      metricsCollecting: !!this.metricsCollector,
      configValid: fs.existsSync(path.join(this.config.projectRoot, this.config.configFile))
    };

    const operational = Object.values(checks).every(check => check);
    
    const recommendations: string[] = [];
    if (!checks.hybridTDDActive) recommendations.push('Initialize HybridTDDSystem');
    if (!checks.tddAgentReady) recommendations.push('Configure TDDAgent');
    if (!checks.metricsCollecting) recommendations.push('Set up MetricsCollector');
    if (!checks.configValid) recommendations.push('Create ae-framework-v2.yml configuration');

    return {
      operational,
      checks,
      recommendations
    };
  }

  /**
   * Get TDD system instance for external use
   */
  getHybridTDDSystem(): HybridTDDSystem | undefined {
    return this.hybridTDD;
  }

  /**
   * Get TDD Agent instance for external use
   */
  getTDDAgent(): TDDAgent | undefined {
    return this.tddAgent;
  }

  /**
   * Get MetricsCollector instance for external use
   */
  getMetricsCollector(): MetricsCollector | undefined {
    return this.metricsCollector;
  }

  /**
   * Generate initial setup report
   */
  generateSetupReport(): string {
    const timestamp = new Date().toISOString();
    
    return `# ae-framework Self-Improvement TDD Setup Report

Generated: ${timestamp}

## Configuration
- **Project**: ${this.config.projectRoot}
- **Config File**: ${this.config.configFile}
- **Target Coverage**: ${this.config.targetCoverage}%
- **Strict Mode**: ${this.config.strictModeEnforcement ? 'Enabled' : 'Disabled'}
- **Real-time Monitoring**: ${this.config.enableRealTimeMonitoring ? 'Enabled' : 'Disabled'}

## Components Status
- **HybridTDDSystem**: ${this.hybridTDD ? '✅ Active' : '❌ Not initialized'}
- **TDDAgent**: ${this.tddAgent ? '✅ Ready' : '❌ Not configured'}
- **MetricsCollector**: ${this.metricsCollector ? '✅ Collecting' : '❌ Not active'}

## Self-Improvement Goals
- TypeScript Errors: 287 → 0
- Test Coverage: → 80%+
- Performance: → 20% improvement
- TDD Compliance: → 95%+

## Next Steps
1. Begin Phase 1: Foundation Analysis & Core Utilities
2. Use NaturalLanguageTaskAdapter for codebase analysis
3. Apply TDD enforcement to core utility fixes
4. Track progress with MetricsCollector
`;
  }
}

// Export factory function for easy integration
export const createSelfImprovementTDDSetup = (config?: Partial<SelfImprovementTDDConfig>) => {
  return new SelfImprovementTDDSetup(config);
};
