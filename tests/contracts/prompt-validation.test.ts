/**
 * Prompt Contract Testing
 * 
 * Validates AI agent outputs against JSON Schema contracts to ensure
 * consistent, structured responses that meet API requirements.
 */

import { describe, it, expect, beforeAll } from 'vitest';
import Ajv from 'ajv';
import addFormats from 'ajv-formats';

interface PromptContract {
  id: string;
  name: string;
  description: string;
  schema: object;
  examples: {
    valid: any[];
    invalid: any[];
  };
}

interface ValidationResult {
  valid: boolean;
  errors?: string[];
  score: number;
}

interface PromptTestSuite {
  contract: PromptContract;
  testCases: Array<{
    input: string;
    expectedOutput: any;
    description: string;
  }>;
}

class PromptContractValidator {
  private ajv: Ajv;
  private contracts: Map<string, PromptContract>;

  constructor() {
    this.ajv = new Ajv({ allErrors: true, strict: false });
    addFormats(this.ajv);
    this.contracts = new Map();
    this.loadContracts();
  }

  private loadContracts(): void {
    // Load predefined contracts for AE Framework
    const contracts: PromptContract[] = [
      {
        id: 'ae-spec-analysis',
        name: 'AE-Spec Analysis Output',
        description: 'Schema for AI agent analysis of AE-Spec documents',
        schema: {
          type: 'object',
          required: ['entities', 'relationships', 'recommendations'],
          properties: {
            entities: {
              type: 'array',
              items: {
                type: 'object',
                required: ['name', 'type', 'fields'],
                properties: {
                  name: { type: 'string', minLength: 1 },
                  type: { enum: ['domain', 'ui', 'api'] },
                  fields: {
                    type: 'array',
                    items: {
                      type: 'object',
                      required: ['name', 'type'],
                      properties: {
                        name: { type: 'string', minLength: 1 },
                        type: { type: 'string', minLength: 1 },
                        required: { type: 'boolean' },
                        validation: { type: 'string' }
                      }
                    }
                  }
                }
              }
            },
            relationships: {
              type: 'array',
              items: {
                type: 'object',
                required: ['from', 'to', 'type'],
                properties: {
                  from: { type: 'string', minLength: 1 },
                  to: { type: 'string', minLength: 1 },
                  type: { enum: ['composition', 'aggregation', 'association'] }
                }
              }
            },
            recommendations: {
              type: 'array',
              items: {
                type: 'object',
                required: ['category', 'priority', 'description'],
                properties: {
                  category: { enum: ['accessibility', 'performance', 'security', 'usability'] },
                  priority: { enum: ['high', 'medium', 'low'] },
                  description: { type: 'string', minLength: 10 }
                }
              }
            }
          }
        },
        examples: {
          valid: [
            {
              entities: [
                {
                  name: 'User',
                  type: 'domain',
                  fields: [
                    { name: 'email', type: 'string', required: true },
                    { name: 'name', type: 'string', required: true }
                  ]
                }
              ],
              relationships: [
                { from: 'User', to: 'Profile', type: 'composition' }
              ],
              recommendations: [
                {
                  category: 'accessibility',
                  priority: 'high',
                  description: 'Add ARIA labels for form inputs'
                }
              ]
            }
          ],
          invalid: [
            { entities: [] }, // Missing required fields
            { entities: [{ name: '', type: 'invalid' }] } // Invalid enum
          ]
        }
      },
      {
        id: 'code-generation-plan',
        name: 'Code Generation Plan',
        description: 'Schema for AI-generated code implementation plans',
        schema: {
          type: 'object',
          required: ['files', 'dependencies', 'steps'],
          properties: {
            files: {
              type: 'array',
              items: {
                type: 'object',
                required: ['path', 'type', 'purpose'],
                properties: {
                  path: { type: 'string', pattern: '^[a-zA-Z0-9\\/\\-_\\.]+$' },
                  type: { enum: ['component', 'service', 'test', 'type', 'style'] },
                  purpose: { type: 'string', minLength: 10 }
                }
              }
            },
            dependencies: {
              type: 'array',
              items: {
                type: 'object',
                required: ['name', 'version', 'purpose'],
                properties: {
                  name: { type: 'string', minLength: 1 },
                  version: { type: 'string', pattern: '^[\\^~]?\\d+\\.\\d+\\.\\d+' },
                  purpose: { type: 'string', minLength: 5 }
                }
              }
            },
            steps: {
              type: 'array',
              minItems: 1,
              items: {
                type: 'object',
                required: ['order', 'action', 'description'],
                properties: {
                  order: { type: 'integer', minimum: 1 },
                  action: { enum: ['create', 'update', 'test', 'validate'] },
                  description: { type: 'string', minLength: 10 }
                }
              }
            }
          }
        },
        examples: {
          valid: [
            {
              files: [
                {
                  path: 'src/components/UserForm.tsx',
                  type: 'component',
                  purpose: 'User registration form component'
                }
              ],
              dependencies: [
                {
                  name: 'react',
                  version: '^18.0.0',
                  purpose: 'UI framework'
                }
              ],
              steps: [
                {
                  order: 1,
                  action: 'create',
                  description: 'Create user form component with validation'
                }
              ]
            }
          ],
          invalid: [
            { files: [], dependencies: [] }, // Missing steps
            { steps: [{ order: 0, action: 'invalid' }] } // Invalid order and action
          ]
        }
      }
    ];

    contracts.forEach(contract => {
      this.contracts.set(contract.id, contract);
    });
  }

  validateAgainstContract(contractId: string, output: any): ValidationResult {
    const contract = this.contracts.get(contractId);
    if (!contract) {
      return {
        valid: false,
        errors: [`Contract '${contractId}' not found`],
        score: 0
      };
    }

    const validate = this.ajv.compile(contract.schema);
    const valid = validate(output);

    if (valid) {
      return {
        valid: true,
        score: 100
      };
    }

    const errors = validate.errors?.map(err => {
      return `${err.instancePath || 'root'}: ${err.message}`;
    }) || [];

    // Calculate partial score based on validation errors
    const score = Math.max(0, 100 - (errors.length * 20));

    return {
      valid: false,
      errors,
      score
    };
  }

  generateTestSuite(contractId: string): PromptTestSuite | null {
    const contract = this.contracts.get(contractId);
    if (!contract) return null;

    return {
      contract,
      testCases: [
        {
          input: 'Analyze this AE-Spec: User { email: string!, name: string! }',
          expectedOutput: contract.examples.valid[0],
          description: 'Should parse simple entity definition'
        },
        {
          input: 'Generate plan for user management system',
          expectedOutput: contract.examples.valid[0],
          description: 'Should create structured implementation plan'
        }
      ]
    };
  }

  runContractTests(contractId: string, testOutputs: any[]): {
    passed: number;
    failed: number;
    results: Array<{
      index: number;
      result: ValidationResult;
    }>;
  } {
    const results = testOutputs.map((output, index) => ({
      index,
      result: this.validateAgainstContract(contractId, output)
    }));

    const passed = results.filter(r => r.result.valid).length;
    const failed = results.length - passed;

    return { passed, failed, results };
  }

  generateContractReport(contractId: string, testResults: any[]): string {
    const contract = this.contracts.get(contractId);
    if (!contract) return 'Contract not found';

    const report = [];
    report.push(`# Prompt Contract Validation Report`);
    report.push('');
    report.push(`**Contract:** ${contract.name}`);
    report.push(`**Description:** ${contract.description}`);
    report.push(`**Generated:** ${new Date().toISOString()}`);
    report.push('');

    const summary = this.runContractTests(contractId, testResults);
    report.push('## Summary');
    report.push(`- Total Tests: ${summary.passed + summary.failed}`);
    report.push(`- Passed: ${summary.passed}`);
    report.push(`- Failed: ${summary.failed}`);
    report.push(`- Success Rate: ${Math.round((summary.passed / (summary.passed + summary.failed)) * 100)}%`);
    report.push('');

    if (summary.failed > 0) {
      report.push('## Failed Validations');
      summary.results
        .filter(r => !r.result.valid)
        .forEach(r => {
          report.push(`### Test ${r.index + 1} (Score: ${r.result.score})`);
          r.result.errors?.forEach(error => {
            report.push(`- ${error}`);
          });
          report.push('');
        });
    }

    return report.join('\n');
  }
}

class MockAIAgent {
  private readonly analysisPattern = [false, false, true, false, false, true, false, false, false, false];
  private analysisIndex = 0;
  private readonly planPattern = [false, false, true, false, false, false, false, false];
  private planIndex = 0;

  async generateAESpecAnalysis(spec: string): Promise<any> {
    // Simulate AI agent output with an intentional, deterministic error cadence
    const hasError = this.analysisPattern[this.analysisIndex++ % this.analysisPattern.length];
    
    if (hasError) {
      return {
        entities: [],
        relationships: 'invalid',
      };
    }

    return {
      entities: [
        {
          name: 'User',
          type: 'domain',
          fields: [
            { name: 'email', type: 'string', required: true },
            { name: 'name', type: 'string', required: true }
          ]
        }
      ],
      relationships: [
        { from: 'User', to: 'Profile', type: 'composition' }
      ],
      recommendations: [
        {
          category: 'accessibility',
          priority: 'high',
          description: 'Add ARIA labels for form inputs'
        }
      ]
    };
  }

  async generateCodePlan(requirements: string): Promise<any> {
    // Deterministic pattern keeps success rate above the 50% contract floor
    const hasError = this.planPattern[this.planIndex++ % this.planPattern.length];
    
    if (hasError) {
      return {
        files: [{ path: '', type: 'invalid' }],
        dependencies: [],
        steps: []
      };
    }

    return {
      files: [
        {
          path: 'src/components/UserForm.tsx',
          type: 'component',
          purpose: 'User registration form component'
        }
      ],
      dependencies: [
        {
          name: 'react',
          version: '^18.0.0',
          purpose: 'UI framework'
        }
      ],
      steps: [
        {
          order: 1,
          action: 'create',
          description: 'Create user form component with validation'
        }
      ]
    };
  }
}

describe('Prompt Contract Testing', () => {
  let validator: PromptContractValidator;
  let mockAgent: MockAIAgent;

  beforeAll(() => {
    validator = new PromptContractValidator();
    mockAgent = new MockAIAgent();
  });

  it('should validate AE-Spec analysis outputs against contract', async () => {
    const outputs = [];
    
    // Generate multiple test outputs
    for (let i = 0; i < 10; i++) {
      const output = await mockAgent.generateAESpecAnalysis('sample spec');
      outputs.push(output);
    }

    const testResults = validator.runContractTests('ae-spec-analysis', outputs);
    
    // Should have reasonable success rate (allowing for intentional errors)
    expect(testResults.passed + testResults.failed).toBe(10);
    expect(testResults.passed).toBeGreaterThanOrEqual(5); // Maintain 50% floor with deterministic mock
    
    console.log(`✅ AE-Spec Analysis: ${testResults.passed}/${testResults.passed + testResults.failed} passed`);
  });

  it('should validate code generation plans against contract', async () => {
    const outputs = [];
    
    for (let i = 0; i < 8; i++) {
      const output = await mockAgent.generateCodePlan('user management system');
      outputs.push(output);
    }

    const testResults = validator.runContractTests('code-generation-plan', outputs);
    
    expect(testResults.passed + testResults.failed).toBe(8);
    expect(testResults.passed).toBeGreaterThanOrEqual(4); // Maintain 50% floor with deterministic mock
    
    console.log(`✅ Code Generation Plans: ${testResults.passed}/${testResults.passed + testResults.failed} passed`);
  });

  it('should reject outputs that violate required fields', () => {
    const invalidOutput = {
      entities: [], // Missing required relationships and recommendations
    };

    const result = validator.validateAgainstContract('ae-spec-analysis', invalidOutput);
    
    expect(result.valid).toBe(false);
    expect(result.errors).toBeDefined();
    expect(result.score).toBeLessThan(100);
  });

  it('should accept valid outputs that meet all contract requirements', () => {
    const validOutput = {
      entities: [
        {
          name: 'User',
          type: 'domain',
          fields: [
            { name: 'email', type: 'string', required: true }
          ]
        }
      ],
      relationships: [
        { from: 'User', to: 'Profile', type: 'composition' }
      ],
      recommendations: [
        {
          category: 'accessibility',
          priority: 'high',
          description: 'Add ARIA labels for form inputs'
        }
      ]
    };

    const result = validator.validateAgainstContract('ae-spec-analysis', validOutput);
    
    expect(result.valid).toBe(true);
    expect(result.score).toBe(100);
  });

  it('should generate comprehensive validation reports', async () => {
    const outputs = [];
    
    // Generate mix of valid and invalid outputs
    for (let i = 0; i < 5; i++) {
      outputs.push(await mockAgent.generateAESpecAnalysis('test spec'));
    }

    const report = validator.generateContractReport('ae-spec-analysis', outputs);
    
    expect(report).toContain('Prompt Contract Validation Report');
    expect(report).toContain('Total Tests: 5');
    expect(report).toContain('Success Rate:');
    
    console.log('📊 Generated validation report');
  });

  it('should handle edge cases gracefully', () => {
    // Test with null/undefined
    const nullResult = validator.validateAgainstContract('ae-spec-analysis', null);
    expect(nullResult.valid).toBe(false);

    // Test with wrong data types
    const stringResult = validator.validateAgainstContract('ae-spec-analysis', 'not an object');
    expect(stringResult.valid).toBe(false);

    // Test with unknown contract
    const unknownResult = validator.validateAgainstContract('nonexistent', {});
    expect(unknownResult.valid).toBe(false);
    expect(unknownResult.errors?.[0]).toContain('not found');
  });

  it('should calculate partial scores for partially valid outputs', () => {
    const partiallyValidOutput = {
      entities: [
        {
          name: 'User',
          type: 'domain',
          fields: [] // Valid structure but empty
        }
      ],
      relationships: [], // Valid but empty
      // Missing recommendations (should reduce score)
    };

    const result = validator.validateAgainstContract('ae-spec-analysis', partiallyValidOutput);
    
    expect(result.valid).toBe(false);
    expect(result.score).toBeGreaterThan(0);
    expect(result.score).toBeLessThan(100);
  });
});

// Export for integration with other tests
export { PromptContractValidator, MockAIAgent };
