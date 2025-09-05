/**
 * MCP Server for Verify Agent
 * Exposes verification tools for Phase 5 of ae-framework
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import { VerifyAgent, VerificationRequest, VerificationType } from '../agents/verify-agent.js';
import {
  CoverageArgsSchema,
  FullVerificationArgsSchema,
  LintingArgsSchema,
  RunTestsArgsSchema,
  SecurityScanArgsSchema,
  TypeCheckingArgsSchema,
  parseOrThrow,
  type CoverageArgs,
  type FullVerificationArgs,
  type LintingArgs,
  type RunTestsArgs,
  type SecurityScanArgs,
  type TypeCheckingArgs,
  PerformanceTestsArgsSchema,
  type PerformanceTestsArgs,
  AccessibilityArgsSchema,
  type AccessibilityArgs,
  VerifyContractsArgsSchema,
  type VerifyContractsArgs,
  VerifySpecificationsArgsSchema,
  type VerifySpecificationsArgs,
  MutationTestsArgsSchema,
  type MutationTestsArgs,
  TraceabilityArgsSchema,
  type TraceabilityArgs,
  GetQualityMetricsArgsSchema,
  type GetQualityMetricsArgs,
} from './schemas.js';
import { readFileSync, existsSync, readdirSync, statSync } from 'fs';
import * as path from 'path';

interface VerifyServerOptions {
  name: string;
  version: string;
}

export class VerifyMCPServer {
  private server: Server;
  private verifyAgent: VerifyAgent;

  constructor(options: VerifyServerOptions) {
    this.server = new Server(
      {
        name: options.name,
        version: options.version,
      },
      {
        capabilities: {
          tools: {},
        },
      }
    );

    this.verifyAgent = new VerifyAgent();
    this.setupHandlers();
  }

  private setupHandlers() {
    this.server.setRequestHandler(ListToolsRequestSchema, async () => ({
      tools: [
        {
          name: 'run_full_verification',
          description: 'Run comprehensive verification suite including all test types, coverage, linting, security, and quality checks',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              verificationTypes: {
                type: 'array',
                items: {
                  type: 'string',
                  enum: ['tests', 'coverage', 'linting', 'typechecking', 'security', 'performance', 'accessibility', 'contracts', 'specifications', 'mutations']
                },
                description: 'Types of verification to run'
              },
              strictMode: {
                type: 'boolean',
                description: 'Stop verification on first failure',
                default: false
              }
            },
            required: ['projectPath', 'verificationTypes']
          }
        },
        {
          name: 'run_tests',
          description: 'Run all types of tests (unit, integration, e2e, property, contract)',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              testTypes: {
                type: 'array',
                items: {
                  type: 'string',
                  enum: ['unit', 'integration', 'e2e', 'property', 'contract']
                },
                description: 'Types of tests to run',
                default: ['unit', 'integration', 'e2e']
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'check_coverage',
          description: 'Analyze code coverage and generate detailed coverage report',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              threshold: {
                type: 'number',
                description: 'Minimum coverage threshold percentage',
                default: 80
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'run_linting',
          description: 'Run ESLint and other linting tools for code quality checks',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              fix: {
                type: 'boolean',
                description: 'Automatically fix fixable issues',
                default: false
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'run_type_checking',
          description: 'Run TypeScript type checking',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              strict: {
                type: 'boolean',
                description: 'Enable strict type checking',
                default: true
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'run_security_scan',
          description: 'Run security vulnerability scanning including dependency checks',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              includeDevDeps: {
                type: 'boolean',
                description: 'Include development dependencies in scan',
                default: true
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'run_performance_tests',
          description: 'Run performance benchmarks and load tests',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              duration: {
                type: 'number',
                description: 'Test duration in seconds',
                default: 30
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'check_accessibility',
          description: 'Run accessibility checks for APIs and interfaces',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              standards: {
                type: 'array',
                items: {
                  type: 'string'
                },
                description: 'Accessibility standards to check against',
                default: ['WCAG2.1']
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'verify_contracts',
          description: 'Verify API contracts and consumer compatibility',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              contractPath: {
                type: 'string',
                description: 'Path to contract files'
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'verify_specifications',
          description: 'Validate specifications (OpenAPI, AsyncAPI, GraphQL, TLA+)',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              specPaths: {
                type: 'array',
                items: {
                  type: 'string'
                },
                description: 'Paths to specification files'
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'run_mutation_tests',
          description: 'Run mutation testing to assess test quality',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              threshold: {
                type: 'number',
                description: 'Minimum mutation score threshold',
                default: 80
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'generate_traceability_matrix',
          description: 'Generate traceability matrix linking requirements to tests and code',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              outputFormat: {
                type: 'string',
                enum: ['json', 'html', 'csv'],
                description: 'Output format for the matrix',
                default: 'json'
              }
            },
            required: ['projectPath']
          }
        },
        {
          name: 'get_quality_metrics',
          description: 'Calculate comprehensive quality metrics',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to the project root directory'
              },
              includeHistory: {
                type: 'boolean',
                description: 'Include historical trend data',
                default: false
              }
            },
            required: ['projectPath']
          }
        }
      ]
    }));

    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;

      try {
        switch (name) {
          case 'run_full_verification':
            return await this.handleFullVerification(args);
          case 'run_tests':
            return await this.handleRunTests(args);
          case 'check_coverage':
            return await this.handleCheckCoverage(args);
          case 'run_linting':
            return await this.handleRunLinting(args);
          case 'run_type_checking':
            return await this.handleRunTypeChecking(args);
          case 'run_security_scan':
            return await this.handleRunSecurityScan(args);
          case 'run_performance_tests':
            return await this.handleRunPerformanceTests(args);
          case 'check_accessibility':
            return await this.handleCheckAccessibility(args);
          case 'verify_contracts':
            return await this.handleVerifyContracts(args);
          case 'verify_specifications':
            return await this.handleVerifySpecifications(args);
          case 'run_mutation_tests':
            return await this.handleRunMutationTests(args);
          case 'generate_traceability_matrix':
            return await this.handleGenerateTraceabilityMatrix(args);
          case 'get_quality_metrics':
            return await this.handleGetQualityMetrics(args);
          default:
            throw new Error(`Unknown tool: ${name}`);
        }
      } catch (error) {
        return {
          content: [
            {
              type: 'text',
              text: `Error executing ${name}: ${(error as Error).message}`
            }
          ]
        };
      }
    });
  }

  private async handleFullVerification(args: unknown) {
    const { projectPath, verificationTypes, strictMode }: FullVerificationArgs = parseOrThrow(FullVerificationArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, verificationTypes);
    request.strictMode = strictMode;
    
    const result = await this.verifyAgent.runFullVerification(request);
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleRunTests(args: unknown) {
    const { projectPath, testTypes }: RunTestsArgs = parseOrThrow(RunTestsArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['tests']);
    
    // Filter test files by type
    request.testFiles = request.testFiles.filter(tf => testTypes.includes(tf.type));
    
    const result = await this.verifyAgent.runTests(request);
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleCheckCoverage(args: unknown) {
    const { projectPath, threshold }: CoverageArgs = parseOrThrow(CoverageArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['coverage']);
    
    const result = await this.verifyAgent.checkCoverage(request);
    result.details.threshold = threshold;
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleRunLinting(args: unknown) {
    const { projectPath, fix }: LintingArgs = parseOrThrow(LintingArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['linting']);
    
    const result = await this.verifyAgent.runLinting(request);
    result.details.fixApplied = fix;
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleRunTypeChecking(args: unknown) {
    const { projectPath, strict }: TypeCheckingArgs = parseOrThrow(TypeCheckingArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['typechecking']);
    
    const result = await this.verifyAgent.runTypeChecking(request);
    result.details.strictMode = strict;
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleRunSecurityScan(args: unknown) {
    const { projectPath, includeDevDeps }: SecurityScanArgs = parseOrThrow(SecurityScanArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['security']);
    
    const result = await this.verifyAgent.runSecurityChecks(request);
    result.details.includeDevDeps = includeDevDeps;
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleRunPerformanceTests(args: unknown) {
    const { projectPath, duration }: PerformanceTestsArgs = parseOrThrow(PerformanceTestsArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['performance']);
    
    const result = await this.verifyAgent.runPerformanceTests(request);
    result.details.testDuration = duration;
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleCheckAccessibility(args: unknown) {
    const { projectPath, standards }: AccessibilityArgs = parseOrThrow(AccessibilityArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['accessibility']);
    
    const result = await this.verifyAgent.checkAccessibility(request);
    result.details.standards = standards;
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleVerifyContracts(args: unknown) {
    const { projectPath, contractPath }: VerifyContractsArgs = parseOrThrow(VerifyContractsArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['contracts']);
    
    if (contractPath) {
      request.testFiles = request.testFiles.filter(tf => 
        tf.type === 'contract' || tf.path.includes(contractPath)
      );
    }
    
    const result = await this.verifyAgent.verifyContracts(request);
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleVerifySpecifications(args: unknown) {
    const { projectPath, specPaths }: VerifySpecificationsArgs = parseOrThrow(VerifySpecificationsArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['specifications']);
    
    if (specPaths && specPaths.length > 0) {
      request.specifications = await this.loadSpecifications(specPaths);
    }
    
    const result = await this.verifyAgent.verifySpecifications(request);
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleRunMutationTests(args: unknown) {
    const { projectPath, threshold }: MutationTestsArgs = parseOrThrow(MutationTestsArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['mutations']);
    
    const result = await this.verifyAgent.runMutationTesting(request);
    result.details.threshold = threshold;
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async handleGenerateTraceabilityMatrix(args: unknown) {
    const { projectPath, outputFormat }: TraceabilityArgs = parseOrThrow(TraceabilityArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, ['specifications']);
    
    const matrix = await this.verifyAgent.buildTraceabilityMatrix(request);
    
    let formattedOutput;
    switch (outputFormat) {
      case 'html':
        formattedOutput = this.formatTraceabilityAsHTML(matrix);
        break;
      case 'csv':
        formattedOutput = this.formatTraceabilityAsCSV(matrix);
        break;
      default:
        formattedOutput = JSON.stringify(matrix, null, 2);
    }
    
    return {
      content: [
        {
          type: 'text',
          text: formattedOutput
        }
      ]
    };
  }

  private async handleGetQualityMetrics(args: unknown) {
    const { projectPath, includeHistory }: GetQualityMetricsArgs = parseOrThrow(GetQualityMetricsArgsSchema, args);
    const request = await this.buildVerificationRequest(projectPath, []);
    
    const metrics = await this.verifyAgent.calculateQualityMetrics(request);
    
    const result = {
      metrics,
      timestamp: new Date().toISOString(),
      projectPath,
      includeHistory
    };
    
    return {
      content: [
        {
          type: 'text',
          text: JSON.stringify(result, null, 2)
        }
      ]
    };
  }

  private async buildVerificationRequest(
    projectPath: string, 
    verificationTypes: VerificationType[]
  ): Promise<VerificationRequest> {
    const codeFiles = await this.loadCodeFiles(projectPath);
    const testFiles = await this.loadTestFiles(projectPath);
    const specifications = await this.loadSpecifications([]);
    
    return {
      codeFiles,
      testFiles,
      specifications,
      verificationTypes
    };
  }

  private async loadCodeFiles(projectPath: string) {
    const codeFiles = [];
    const srcPath = path.join(projectPath, 'src');
    
    if (existsSync(srcPath)) {
      const files = this.findFiles(srcPath, ['.ts', '.js', '.tsx', '.jsx']);
      
      for (const filePath of files) {
        try {
          const content = readFileSync(filePath, 'utf-8');
          const ext = path.extname(filePath);
          const language = ext === '.ts' || ext === '.tsx' ? 'typescript' : 'javascript';
          
          codeFiles.push({
            path: filePath,
            content,
            language
          });
        } catch (error) {
          console.warn(`Could not read file ${filePath}: ${(error as Error).message}`);
        }
      }
    }
    
    return codeFiles;
  }

  private async loadTestFiles(projectPath: string) {
    const testFiles = [];
    const testPaths = [
      path.join(projectPath, 'tests'),
      path.join(projectPath, 'test'),
      path.join(projectPath, '__tests__'),
      path.join(projectPath, 'src')
    ];
    
    for (const testPath of testPaths) {
      if (existsSync(testPath)) {
        const files = this.findFiles(testPath, ['.test.ts', '.test.js', '.spec.ts', '.spec.js', '.pbt.test.ts']);
        
        for (const filePath of files) {
          try {
            const content = readFileSync(filePath, 'utf-8');
            const fileName = path.basename(filePath);
            
            let type: 'unit' | 'integration' | 'e2e' | 'property' | 'contract' = 'unit';
            
            if (fileName.includes('integration') || fileName.includes('int.')) {
              type = 'integration';
            } else if (fileName.includes('e2e') || fileName.includes('end-to-end')) {
              type = 'e2e';
            } else if (fileName.includes('pbt') || fileName.includes('property')) {
              type = 'property';
            } else if (fileName.includes('contract') || fileName.includes('pact')) {
              type = 'contract';
            }
            
            testFiles.push({
              path: filePath,
              content,
              type
            });
          } catch (error) {
            console.warn(`Could not read test file ${filePath}: ${(error as Error).message}`);
          }
        }
      }
    }
    
    return testFiles;
  }

  private async loadSpecifications(specPaths: string[]) {
    const specifications = [];
    
    // Default specification paths
    const defaultPaths = [
      'specs/openapi/api.yaml',
      'specs/openapi/api.json',
      'specs/asyncapi/events.yaml',
      'specs/formal/tla+/*.tla',
      'specs/graphql/schema.graphql'
    ];
    
    const pathsToCheck = specPaths.length > 0 ? specPaths : defaultPaths;
    
    for (const specPath of pathsToCheck) {
      if (existsSync(specPath)) {
        try {
          const content = readFileSync(specPath, 'utf-8');
          const ext = path.extname(specPath);
          
          let type: 'openapi' | 'asyncapi' | 'graphql' | 'tla' | 'alloy' = 'openapi';
          
          if (specPath.includes('asyncapi')) {
            type = 'asyncapi';
          } else if (ext === '.graphql') {
            type = 'graphql';
          } else if (ext === '.tla') {
            type = 'tla';
          } else if (ext === '.als') {
            type = 'alloy';
          }
          
          specifications.push({
            type,
            content,
            path: specPath
          });
        } catch (error) {
          console.warn(`Could not read specification ${specPath}: ${(error as Error).message}`);
        }
      }
    }
    
    return specifications;
  }

  private findFiles(dir: string, extensions: string[]): string[] {
    const files: string[] = [];
    
    try {
      const items = readdirSync(dir);
      
      for (const item of items) {
        const fullPath = path.join(dir, item);
        const stat = statSync(fullPath);
        
        if (stat.isDirectory()) {
          files.push(...this.findFiles(fullPath, extensions));
        } else if (stat.isFile()) {
          const hasMatchingExtension = extensions.some(ext => 
            item.endsWith(ext)
          );
          
          if (hasMatchingExtension) {
            files.push(fullPath);
          }
        }
      }
    } catch (error) {
      console.warn(`Could not read directory ${dir}: ${(error as Error).message}`);
    }
    
    return files;
  }

  private formatTraceabilityAsHTML(matrix: { coverage: number; requirements: { id: string; description: string; covered: boolean; linkedTo: string[] }[]; tests?: { id: string; description: string; covered: boolean; linkedTo: string[] }[]; code?: { id: string; description: string; covered: boolean; linkedTo: string[] }[] }): string {
    return `
<!DOCTYPE html>
<html>
<head>
    <title>Traceability Matrix</title>
    <style>
        table { border-collapse: collapse; width: 100%; }
        th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
        th { background-color: #f2f2f2; }
        .covered { background-color: #d4edda; }
        .not-covered { background-color: #f8d7da; }
    </style>
</head>
<body>
    <h1>Traceability Matrix</h1>
    <p>Coverage: ${matrix.coverage}%</p>
    <table>
        <tr>
            <th>Type</th>
            <th>ID</th>
            <th>Description</th>
            <th>Covered</th>
            <th>Linked To</th>
        </tr>
        ${matrix.requirements.map((req) => `
            <tr class="${req.covered ? 'covered' : 'not-covered'}">
                <td>Requirement</td>
                <td>${req.id}</td>
                <td>${req.description}</td>
                <td>${req.covered ? 'Yes' : 'No'}</td>
                <td>${req.linkedTo.join(', ')}</td>
            </tr>
        `).join('')}
    </table>
</body>
</html>`;
  }

  private formatTraceabilityAsCSV(matrix: { requirements: { id: string; description: string; covered: boolean; linkedTo: string[] }[]; tests: { id: string; description: string; covered: boolean; linkedTo: string[] }[]; code: { id: string; description: string; covered: boolean; linkedTo: string[] }[] }): string {
    const header = 'Type,ID,Description,Covered,LinkedTo\n';
    const rows = [
      ...matrix.requirements.map((req) => 
        `Requirement,${req.id},"${req.description}",${req.covered},"${req.linkedTo.join(';')}"`
      ),
      ...matrix.tests.map((test) => 
        `Test,${test.id},"${test.description}",${test.covered},"${test.linkedTo.join(';')}"`
      ),
      ...matrix.code.map((code) => 
        `Code,${code.id},"${code.description}",${code.covered},"${code.linkedTo.join(';')}"`
      )
    ];
    
    return header + rows.join('\n');
  }

  async run() {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
  }
}

// Start the server if this file is run directly
if (typeof require !== 'undefined' && require.main === module) {
  const server = new VerifyMCPServer({
    name: 'ae-framework-verify-agent',
    version: '1.0.0'
  });

  server.run().catch((error) => {
    console.error('Failed to start Verify MCP Server:', error);
    process.exit(1);
  });
}
