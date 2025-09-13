import { readFileSync, existsSync } from 'fs';
import * as yaml from 'js-yaml';
import * as path from 'path';
import type { AEFrameworkConfig } from '../types.js';

export class ConfigLoader {
  static load(configPath?: string): AEFrameworkConfig {
    const possiblePaths = [
      configPath,
      'ae-framework.yml',
      'ae-framework.yaml', 
      '.ae-framework.yml',
      '.ae-framework.yaml',
      path.join(process.cwd(), 'ae-framework.yml'),
      path.join(process.cwd(), '.ae-framework.yml')
    ].filter(Boolean) as string[];

    for (const configFile of possiblePaths) {
      if (existsSync(configFile)) {
        try {
          const configContent = readFileSync(configFile, 'utf8');
          const config = yaml.load(configContent) as AEFrameworkConfig;
          
          // Validate and set defaults
          return this.validateAndSetDefaults(config);
        } catch (error) {
          console.warn(`Warning: Could not parse config file ${configFile}: ${error}`);
        }
      }
    }

    // Return default configuration if no config file found
    return this.getDefaultConfig();
  }

  private static validateAndSetDefaults(config: Partial<AEFrameworkConfig>): AEFrameworkConfig {
    const defaultConfig = this.getDefaultConfig();

    return {
      version: config.version || defaultConfig.version,
      name: config.name || defaultConfig.name,
      description: config.description || defaultConfig.description,
      phases: { ...defaultConfig.phases, ...config.phases },
      guards: config.guards || defaultConfig.guards,
      cli: { ...defaultConfig.cli, ...config.cli },
      templates: { ...defaultConfig.templates, ...config.templates },
      integrations: { ...defaultConfig.integrations, ...config.integrations },
      metrics: { ...defaultConfig.metrics, ...config.metrics }
    };
  }

  private static getDefaultConfig(): AEFrameworkConfig {
    return {
      version: "1.0",
      name: "ae-framework",
      description: "AI-Agent Enabled Framework with TDD enforcement",
      phases: {
        "1-intent": {
          name: "Intent Definition",
          description: "Define requirements, specifications, and API contracts",
          required_artifacts: ["specs/gates.yaml"],
          validation: ["check_requirements_completeness"]
        },
        "2-formal": {
          name: "Formal Specification",
          description: "Create formal specifications using TLA+, state charts",
          required_artifacts: ["specs/formal/tla+/*.tla"],
          validation: ["validate_formal_specs"]
        },
        "3-tests": {
          name: "Test-First Development", 
          description: "Write tests before implementation (RED phase)",
          required_artifacts: ["tests/**/*.test.ts"],
          validation: ["ensure_tests_exist", "run_tests_expect_red"],
          enforce_red_first: true,
          block_code_without_test: true
        },
        "4-code": {
          name: "Implementation",
          description: "Implement code to make tests pass (GREEN phase)",
          required_artifacts: ["src/**/*.ts"],
          validation: ["ensure_tests_pass", "check_code_coverage"],
          prerequisites: [{
            phase: "3-tests",
            status: "completed", 
            validation: "tests_are_red"
          }]
        },
        "5-verify": {
          name: "Verification & Validation",
          description: "Comprehensive testing and verification",
          required_artifacts: ["verify/traceability.sh"],
          validation: ["run_full_test_suite", "verify_traceability"],
          mandatory_test_run: true,
          coverage_threshold: 80
        },
        "6-operate": {
          name: "Operations Setup",
          description: "Deployment, monitoring, and operational concerns", 
          required_artifacts: ["Dockerfile", "compose.yaml"],
          validation: ["validate_deployment_configs"]
        }
      },
      guards: [
        {
          name: "TDD Guard",
          description: "Prevent code creation without corresponding tests",
          rule: "For each src/**/*.ts file, a corresponding tests/**/*.test.ts must exist",
          enforcement: "strict"
        },
        {
          name: "Test Execution Guard",
          description: "Ensure all tests pass before commits", 
          rule: "All tests must be GREEN before git commit",
          enforcement: "strict"
        },
        {
          name: "RED-GREEN Cycle Guard",
          description: "Enforce RED-GREEN-REFACTOR cycle",
          rule: "Tests must be RED before implementation, GREEN after",
          enforcement: "strict"
        },
        {
          name: "Coverage Guard",
          description: "Maintain minimum code coverage",
          rule: "Code coverage must be >= 80%",
          enforcement: "warning"
        }
      ],
      cli: {
        checkpoint_validation: true,
        interactive_mode: true,
        auto_validation: true,
        commands: {
          check: {
            description: "Validate current phase requirements",
            usage: "ae-framework check --phase <phase-name>"
          },
          next: {
            description: "Move to next phase with validation",
            usage: "ae-framework next"
          },
          guard: {
            description: "Run specific guard validation",
            usage: "ae-framework guard --name <guard-name>"
          }
        }
      },
      templates: {
        test_first: {
          enabled: true,
          path: "templates/test-first/"
        },
        phase_transitions: {
          enabled: true,
          require_validation: true
        },
        standard_prompts: {
          enabled: true,
          path: "templates/prompts/"
        }
      },
      integrations: {
        git: {
          pre_commit_hooks: true,
          prevent_commit_on_red: true
        },
        ide: {
          vscode_extension: true,
          guard_notifications: true
        },
        ci_cd: {
          validate_on_push: true,
          block_merge_on_violations: true
        }
      },
      metrics: {
        track_tdd_violations: true,
        phase_timing: true,
        coverage_trends: true,
        export: {
          format: "json",
          path: "metrics/"
        }
      }
    };
  }
}
