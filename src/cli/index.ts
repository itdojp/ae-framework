#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import { PhaseValidator } from './validators/PhaseValidator.js';
import { createSpecCommand } from './spec-cli.js';
import { createCodegenCommand } from './codegen-cli.js';
import { CEGISCli } from './cegis-cli.js';
import { GuardRunner } from './guards/GuardRunner.js';
import { ConfigLoader } from './config/ConfigLoader.js';
// import { MetricsCollector } from './metrics/MetricsCollector.js';  // TODO: Enable when metrics tracking is implemented
import { AEFrameworkConfig, Phase } from './types.js';
import { createHybridIntentSystem } from '../integration/hybrid-intent-system.js';
import { TaskRequest, TaskResponse, TaskHandler } from '../agents/task-types.js';
import { createNaturalLanguageTaskHandler } from '../agents/natural-language-task-adapter.js';
import { createUserStoriesTaskHandler } from '../agents/user-stories-task-adapter.js';
import { createValidationTaskHandler } from '../agents/validation-task-adapter.js';
import { createDomainModelingTaskHandler } from '../agents/domain-modeling-task-adapter.js';
import { UIScaffoldGenerator } from '../generators/ui-scaffold-generator.js';
import { Phase6Telemetry } from '../telemetry/phase6-metrics.js';
import '../telemetry/telemetry-setup.js'; // Initialize telemetry
import * as fs from 'fs';
import * as path from 'path';
import { createSecurityCommand } from './security-cli.js';

const program = new Command();

// TaskResult is now TaskResponse from the adapters (addressing Copilot review comment 2280080078)
type TaskResult = TaskResponse;

class AEFrameworkCLI {
  private config: AEFrameworkConfig;
  private phaseValidator: PhaseValidator;
  private guardRunner: GuardRunner;
  private intentSystem: any;
  // private metricsCollector: MetricsCollector;  // TODO: use for metrics tracking
  public naturalLanguageHandler: TaskHandler;
  public userStoriesHandler: TaskHandler;
  public validationHandler: TaskHandler;
  public domainModelingHandler: TaskHandler;
  public uiHandler: TaskHandler;

  constructor() {
    this.config = ConfigLoader.load();
    this.phaseValidator = new PhaseValidator(this.config);
    this.guardRunner = new GuardRunner(this.config);
    this.intentSystem = createHybridIntentSystem({
      enableCLI: true,
      enableMCPServer: false, // Disabled for CLI mode
      enableClaudeCodeIntegration: false,
      enforceRealTime: false,
      strictMode: false,
    });
    // this.metricsCollector = new MetricsCollector(this.config);  // TODO: use for metrics tracking
    
    // Initialize Task Tool handlers with proper types
    this.naturalLanguageHandler = createNaturalLanguageTaskHandler();
    this.userStoriesHandler = createUserStoriesTaskHandler();
    this.validationHandler = createValidationTaskHandler();
    this.domainModelingHandler = createDomainModelingTaskHandler();
    this.uiHandler = {
      handleTask: async (request: TaskRequest): Promise<TaskResponse> => {
        return this.handleUIScaffoldTask(request);
      }
    };
  }

  async checkPhase(phaseName: string): Promise<void> {
    console.log(chalk.blue(`🔍 Checking phase: ${phaseName}`));
    
    const phase = this.config.phases[phaseName];
    if (!phase) {
      console.log(chalk.red(`❌ Unknown phase: ${phaseName}`));
      process.exit(1);
    }

    const results = await this.phaseValidator.validate(phase);
    
    if (results.success) {
      console.log(chalk.green(`✅ Phase ${phaseName} validation passed`));
      this.displayResults(results.details);
      console.log(chalk.green(`⏭️  Ready for next phase`));
    } else {
      console.log(chalk.red(`❌ Phase ${phaseName} validation failed`));
      this.displayResults(results.details);
      process.exit(1);
    }
  }

  async runGuards(guardName?: string): Promise<void> {
    const guards = guardName 
      ? [this.config.guards.find(g => g.name === guardName)].filter(Boolean)
      : this.config.guards;

    if (guards.length === 0) {
      console.log(chalk.yellow(`⚠️  No guards found`));
      return;
    }

    console.log(chalk.blue(`🛡️  Running ${guards.length} guards...`));

    let allPassed = true;
    for (const guard of guards) {
      const result = await this.guardRunner.run(guard!);
      
      if (result.success) {
        console.log(chalk.green(`✅ ${guard!.name}: PASSED`));
      } else {
        console.log(chalk.red(`❌ ${guard!.name}: FAILED`));
        console.log(chalk.red(`   ${result.message}`));
        
        if (guard!.enforcement === 'strict') {
          allPassed = false;
        }
      }
    }

    if (!allPassed) {
      process.exit(1);
    }
  }

  async runIntent(options: { analyze?: boolean; validate?: boolean; sources?: string }): Promise<void> {
    console.log(chalk.blue('🎯 Running Intent Analysis...'));
    
    try {
      if (options.validate) {
        console.log(chalk.blue('🔍 Validating Intent completeness...'));
        const result = await this.intentSystem.handleIntentRequest({
          type: 'cli',
          data: { command: 'validate', sources: options.sources || [] }
        });
        
        if (result.response.score > 0.8) {
          console.log(chalk.green(`✅ Intent validation passed: ${Math.round(result.response.score * 100)}%`));
        } else {
          console.log(chalk.red(`❌ Intent validation failed: ${Math.round(result.response.score * 100)}%`));
          console.log(chalk.yellow('Missing areas:'));
          result.response.missingAreas?.forEach((area: string) => {
            console.log(chalk.yellow(`  • ${area}`));
          });
          process.exit(1);
        }
      } else {
        console.log(chalk.blue('📋 Analyzing requirements and extracting intent...'));
        const result = await this.intentSystem.handleIntentRequest({
          type: 'cli',
          data: { command: 'analyze', sources: options.sources || [] }
        });
        
        console.log(chalk.green('✅ Intent analysis completed'));
        if (result.response.requirements) {
          console.log(chalk.green(`   Found ${result.response.requirements.length} requirements`));
        }
        
        if (result.followUp) {
          console.log(chalk.cyan('\n📋 Next steps:'));
          result.followUp.forEach((step: string) => {
            console.log(chalk.cyan(`  • ${step}`));
          });
        }
      }
    } catch (error) {
      console.log(chalk.red(`❌ Intent analysis failed: ${error}`));
      process.exit(1);
    }
  }

  // Extracted method to reduce code duplication (addressing review comment)
  public handleProgressBlocking(result: TaskResult): void {
    if (result.recommendations.length > 0) {
      console.log(chalk.yellow('\n💡 Recommendations:'));
      result.recommendations.forEach((rec: string) => console.log(chalk.yellow(`• ${rec}`)));
    }
    
    if (result.nextActions.length > 0) {
      console.log(chalk.cyan('\n⏭️ Next Actions:'));
      result.nextActions.forEach((action: string) => console.log(chalk.cyan(`• ${action}`)));
    }
    
    if (result.warnings.length > 0) {
      console.log(chalk.red('\n⚠️ Warnings:'));
      result.warnings.forEach((warning: string) => console.log(chalk.red(`• ${warning}`)));
    }
    
    if (result.shouldBlockProgress) {
      console.log(chalk.red('\n🚫 Progress blocked - address critical issues before proceeding'));
      process.exit(1);
    }
  }

  async nextPhase(): Promise<void> {
    const currentPhase = await this.detectCurrentPhase();
    const nextPhase = this.getNextPhase(currentPhase);
    
    if (!nextPhase) {
      console.log(chalk.green(`🎉 All phases completed!`));
      return;
    }

    console.log(chalk.blue(`📋 Current phase: ${currentPhase}`));
    console.log(chalk.blue(`⏭️  Next phase: ${nextPhase}`));

    // Validate prerequisites
    const phase = this.config.phases[nextPhase];
    if (!phase) {
      console.error(chalk.red(`❌ Phase configuration not found: ${nextPhase}`));
      return;
    }
    
    if (phase.prerequisites) {
      for (const prereq of phase.prerequisites) {
        const valid = await this.phaseValidator.validatePrerequisite(prereq);
        if (!valid.success) {
          console.log(chalk.red(`❌ Prerequisite not met: ${prereq.phase}`));
          console.log(chalk.red(`   ${valid.message}`));
          process.exit(1);
        }
      }
    }

    console.log(chalk.green(`✅ Prerequisites satisfied`));
    console.log(chalk.blue(`🚀 Ready to start phase: ${nextPhase}`));
    this.displayPhaseRequirements(phase as any);
  }

  async detectCurrentPhase(): Promise<string> {
    // Logic to detect current phase based on existing artifacts
    const phases = Object.keys(this.config.phases);
    
    for (let i = phases.length - 1; i >= 0; i--) {
      const phaseName = phases[i];
      if (!phaseName) continue;
      
      const phase = this.config.phases[phaseName];
      if (!phase) continue;
      const hasArtifacts = await this.phaseValidator.hasRequiredArtifacts(phase);
      if (hasArtifacts) {
        return phaseName;
      }
    }
    
    const firstPhase = phases[0];
    if (!firstPhase) {
      throw new Error('No phases configured');
    }
    return firstPhase; // Default to first phase
  }

  getNextPhase(currentPhase: string): string | null {
    const phases = Object.keys(this.config.phases);
    const currentIndex = phases.indexOf(currentPhase);
    return currentIndex < phases.length - 1 ? (phases[currentIndex + 1] || null) : null;
  }

  displayResults(details: Array<{ check: string; passed: boolean; message?: string }>): void {
    details.forEach(detail => {
      const icon = detail.passed ? '✅' : '❌';
      const color = detail.passed ? chalk.green : chalk.red;
      console.log(color(`  ${icon} ${detail.check}`));
      if (detail.message) {
        console.log(color(`     ${detail.message}`));
      }
    });
  }

  displayPhaseRequirements(phase: Phase): void {
    console.log(chalk.cyan(`\n📋 Phase Requirements:`));
    console.log(chalk.cyan(`   ${phase.description}`));
    
    if (phase.required_artifacts) {
      console.log(chalk.cyan(`\n📁 Required Artifacts:`));
      phase.required_artifacts.forEach(artifact => {
        console.log(chalk.cyan(`   • ${artifact}`));
      });
    }

    if (phase.validation) {
      console.log(chalk.cyan(`\n🔍 Validations:`));
      phase.validation.forEach(validation => {
        console.log(chalk.cyan(`   • ${validation}`));
      });
    }
  }

  async handleUIScaffoldTask(request: TaskRequest): Promise<TaskResponse> {
    return await Phase6Telemetry.instrumentScaffoldOperation(
      'ui_scaffold_task',
      async () => {
        const stateFile = path.join(process.cwd(), '.ae', 'phase-state.json');
        
        if (!fs.existsSync(stateFile)) {
          return {
            summary: 'Phase state file not found',
            analysis: 'No .ae/phase-state.json found. Please run domain modeling first.',
            recommendations: ['Run ae-framework domain-model to create phase state'],
            nextActions: ['Set up project with ae-framework'],
            warnings: ['Cannot generate UI without domain model'],
            shouldBlockProgress: true
          };
        }

        const phaseState = JSON.parse(fs.readFileSync(stateFile, 'utf8'));
        const outputDir = path.join(process.cwd(), 'src', 'ui', 'components', 'generated');
        
        const generator = new UIScaffoldGenerator(phaseState, { outputDir });
        const results = await generator.generateAll();
        
        const successCount = Object.values(results).filter(r => r.success).length;
        const totalCount = Object.keys(results).length;
        const totalFiles = Object.values(results).reduce((sum, r) => sum + r.files.length, 0);

        // Record quality metrics
        Phase6Telemetry.recordQualityMetrics({
          coverage: totalFiles > 0 ? (successCount / totalCount) * 100 : 0,
        });

        return {
          summary: `Generated ${totalFiles} files for ${successCount}/${totalCount} entities`,
          analysis: `UI scaffold generation completed:\n${Object.entries(results).map(([entity, result]) => 
            `  • ${entity}: ${result.success ? `✅ ${result.files.length} files` : `❌ ${result.error}`}`
          ).join('\n')}`,
          recommendations: successCount < totalCount ? 
            ['Review failed entities and fix domain model issues'] : 
            ['Run npm run lint to ensure code quality', 'Test generated components'],
          nextActions: ['Review generated components', 'Customize as needed', 'Run quality gates'],
          warnings: successCount < totalCount ? 
            [`${totalCount - successCount} entities failed to generate`] : [],
          shouldBlockProgress: successCount === 0
        };
      },
      {
        request_type: request.subagent_type,
        sources: request.prompt,
      }
    );
  }
}

// CLI Command definitions
program
  .name('ae-framework')
  .description('AI-Agent Enabled Framework CLI')
  .version('1.0.0');

program
  .command('check')
  .description('Validate current phase requirements')
  .option('-p, --phase <phase>', 'Specific phase to check')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    
    if (options.phase) {
      await cli.checkPhase(options.phase);
    } else {
      const currentPhase = await cli.detectCurrentPhase();
      await cli.checkPhase(currentPhase);
    }
  });

program
  .command('guard')
  .description('Run guard validations')
  .option('-n, --name <name>', 'Specific guard to run')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    await cli.runGuards(options.name);
  });

program
  .command('next')
  .description('Move to next phase with validation')
  .action(async () => {
    const cli = new AEFrameworkCLI();
    await cli.nextPhase();
  });

program
  .command('tdd')
  .description('Run TDD cycle validation')
  .action(async () => {
    const cli = new AEFrameworkCLI();
    console.log(chalk.blue('🔄 Validating TDD cycle...'));
    
    // Check TDD Guards
    await cli.runGuards('TDD Guard');
    await cli.runGuards('Test Execution Guard');
    await cli.runGuards('RED-GREEN Cycle Guard');
    
    console.log(chalk.green('✅ TDD cycle validation complete'));
  });

program
  .command('intent')
  .description('Run Intent analysis for Phase 1')
  .option('--analyze', 'Analyze requirements and extract intent')
  .option('--validate', 'Validate Intent completeness')
  .option('--sources <sources>', 'Requirement sources (comma-separated paths)')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    await cli.runIntent(options);
  });

// Phase 2: Natural Language Requirements CLI
program
  .command('natural-language')
  .description('Process natural language requirements (Phase 2)')
  .option('--analyze', 'Analyze natural language requirements')
  .option('--extract-entities', 'Extract business entities from requirements')
  .option('--validate-completeness', 'Validate requirements completeness')
  .option('--sources <sources>', 'Source files or text to process')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    console.log(chalk.blue('🔍 Processing Natural Language Requirements...'));
    
    const taskType = options.analyze ? 'analyze-requirements' :
                    options.extractEntities ? 'extract-entities' :
                    options.validateCompleteness ? 'validate-completeness' :
                    'analyze-requirements';
    
    const request = {
      description: `Natural language processing: ${taskType}`,
      prompt: options.sources || 'Process available requirements documents',
      subagent_type: 'natural-language-processing',
    };
    
    try {
      const result: TaskResult = await cli.naturalLanguageHandler.handleTask(request);
      console.log(chalk.green(`✅ ${result.summary}`));
      console.log(chalk.blue('\n📊 Analysis:'));
      console.log(result.analysis);
      
      cli.handleProgressBlocking(result);
    } catch (error) {
      console.log(chalk.red(`❌ Error: ${error}`));
      process.exit(1);
    }
  });

// Phase 3: User Stories CLI
program
  .command('user-stories')
  .description('Generate and manage user stories (Phase 3)')
  .option('--generate', 'Generate user stories from requirements')
  .option('--validate', 'Validate existing user stories')
  .option('--prioritize', 'Prioritize user stories')
  .option('--estimate', 'Estimate user story complexity')
  .option('--sources <sources>', 'Source files or requirements to process')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    console.log(chalk.blue('📝 Processing User Stories...'));
    
    const taskType = options.generate ? 'generate-stories' :
                    options.validate ? 'validate-stories' :
                    options.prioritize ? 'prioritize-stories' :
                    options.estimate ? 'estimate-stories' :
                    'generate-stories';
    
    const request = {
      description: `User stories processing: ${taskType}`,
      prompt: options.sources || 'Process available requirements for user story generation',
      subagent_type: 'user-stories-processing',
    };
    
    try {
      const result: TaskResult = await cli.userStoriesHandler.handleTask(request);
      console.log(chalk.green(`✅ ${result.summary}`));
      console.log(chalk.blue('\n📊 Analysis:'));
      console.log(result.analysis);
      
      cli.handleProgressBlocking(result);
    } catch (error) {
      console.log(chalk.red(`❌ Error: ${error}`));
      process.exit(1);
    }
  });

// Phase 4: Validation CLI
program
  .command('validate')
  .description('Validate requirements, stories, and specifications (Phase 4)')
  .option('--requirements', 'Validate requirements')
  .option('--stories', 'Validate user stories')
  .option('--specifications', 'Validate specifications')
  .option('--traceability', 'Validate traceability')
  .option('--completeness', 'Validate completeness')
  .option('--sources <sources>', 'Source files to validate')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    console.log(chalk.blue('🔍 Running Validation...'));
    
    const taskType = options.requirements ? 'validate-requirements' :
                    options.stories ? 'validate-user-stories' :
                    options.specifications ? 'validate-specifications' :
                    options.traceability ? 'validate-traceability' :
                    options.completeness ? 'validate-completeness' :
                    'validate-requirements';
    
    const request = {
      description: `Validation: ${taskType}`,
      prompt: options.sources || 'Validate available artifacts',
      subagent_type: 'validation-processing',
    };
    
    try {
      const result: TaskResult = await cli.validationHandler.handleTask(request);
      console.log(chalk.green(`✅ ${result.summary}`));
      console.log(chalk.blue('\n📊 Analysis:'));
      console.log(result.analysis);
      
      cli.handleProgressBlocking(result);
    } catch (error) {
      console.log(chalk.red(`❌ Error: ${error}`));
      process.exit(1);
    }
  });

// Phase 5: Domain Modeling CLI
program
  .command('domain-model')
  .description('Create and validate domain models (Phase 5)')
  .option('--analyze', 'Analyze domain')
  .option('--entities', 'Identify entities')
  .option('--aggregates', 'Model aggregates')
  .option('--contexts', 'Define bounded contexts')
  .option('--rules', 'Extract business rules')
  .option('--language', 'Create ubiquitous language')
  .option('--sources <sources>', 'Source files or requirements to process')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    console.log(chalk.blue('🏗️ Processing Domain Model...'));
    
    const taskType = options.analyze ? 'analyze-domain' :
                    options.entities ? 'identify-entities' :
                    options.aggregates ? 'model-aggregates' :
                    options.contexts ? 'define-bounded-contexts' :
                    options.rules ? 'extract-business-rules' :
                    options.language ? 'create-ubiquitous-language' :
                    'analyze-domain';
    
    const request = {
      description: `Domain modeling: ${taskType}`,
      prompt: options.sources || 'Analyze domain based on available requirements and stories',
      subagent_type: 'domain-modeling-processing',
    };
    
    try {
      const result: TaskResult = await cli.domainModelingHandler.handleTask(request);
      console.log(chalk.green(`✅ ${result.summary}`));
      console.log(chalk.blue('\n📊 Analysis:'));
      console.log(result.analysis);
      
      cli.handleProgressBlocking(result);
    } catch (error) {
      console.log(chalk.red(`❌ Error: ${error}`));
      process.exit(1);
    }
  });

// Phase 6: UI Scaffold CLI
program
  .command('ui-scaffold')
  .description('Generate UI components from domain model (Phase 6)')
  .option('--components', 'Generate React components')
  .option('--state', 'Design state architecture')
  .option('--tokens', 'Integrate design tokens')
  .option('--a11y', 'Validate accessibility')
  .option('--sources <sources>', 'Source files or globs')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    console.log(chalk.blue('🎨 Generating UI Components...'));
    
    const taskType = options.components ? 'generate-components' :
                    options.state ? 'design-state' :
                    options.tokens ? 'integrate-design-tokens' :
                    options.a11y ? 'validate-accessibility' :
                    'generate-components';

    const request = {
      description: `UI/UX processing: ${taskType}`,
      prompt: options.sources || 'Process available domain model and user stories',
      subagent_type: 'ui-processing',
    };

    try {
      const result = await cli.uiHandler.handleTask(request);
      console.log(chalk.green(`✅ ${result.summary}`));
      console.log(chalk.blue('\n🎨 UI Analysis:'));
      console.log(result.analysis);
      cli.handleProgressBlocking(result);
    } catch (error) {
      console.log(chalk.red(`❌ Error: ${error}`));
      process.exit(1);
    }
  });

// Add spec commands
program.addCommand(createSpecCommand());

// Add codegen commands
program.addCommand(createCodegenCommand());

// Add CEGIS auto-fix commands
const cegisCli = new CEGISCli();
program.addCommand(cegisCli.createCommand());

// Add enhanced state management commands
import { createEnhancedStateCommand } from './enhanced-state-cli.js';
program.addCommand(createEnhancedStateCommand());

// Add circuit breaker commands
import { createCircuitBreakerCommand } from './circuit-breaker-cli.js';
program.addCommand(createCircuitBreakerCommand());

// Security commands
program.addCommand(createSecurityCommand());

// Quality gates commands
import { createQualityCommand } from './quality-cli.js';
program.addCommand(createQualityCommand());

// Conformance verification commands  
import { ConformanceCli } from './conformance-cli.js';
const conformanceCli = new ConformanceCli();
program.addCommand(conformanceCli.createCommand());

// Integration testing commands
import { IntegrationTestingCli } from './integration-cli.js';
const integrationCli = new IntegrationTestingCli();
program.addCommand(integrationCli.createCommand());

// Resilience commands
import { createResilienceCommand } from './resilience-cli.js';
program.addCommand(createResilienceCommand());

// SBOM commands
import { createSBOMCommand } from './sbom-cli.js';
program.addCommand(createSBOMCommand());

// Agent commands
import { agentComplete } from '../commands/agent/complete.js';
program
  .command('agent:complete')
  .description('LLM completion for quick verification')
  .option('--prompt <prompt>', 'Prompt to send to LLM (required)')
  .option('--system <system>', 'System message for LLM (optional)')
  .action(async (options) => {
    if (!options.prompt) {
      console.error(chalk.red('❌ --prompt is required'));
      process.exit(1);
    }
    await agentComplete(options.prompt, options.system);
  });

program.parse();

export { AEFrameworkCLI };