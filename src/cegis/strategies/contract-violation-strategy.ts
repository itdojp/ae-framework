/**
 * Contract Violation Fix Strategy
 * Phase 2.1: Automatic fixes for runtime conformance violations
 */

import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';

export class ContractViolationFixStrategy extends BaseFixStrategy {
  readonly name = 'Contract Violation Fix';
  readonly category: FailureCategory = 'contract_violation';
  readonly confidence = 0.8;
  readonly riskLevel = 2;
  readonly description = 'Automatically fixes runtime contract violations by updating validation schemas and adding proper data transformations';

  async canApply(failure: FailureArtifact): Promise<boolean> {
    return failure.category === 'contract_violation' && 
           !!failure.evidence.errorMessage &&
           failure.metadata.environment?.contractName;
  }

  async generateFix(failure: FailureArtifact): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const contractName = failure.metadata.environment?.contractName;
    const violationType = failure.metadata.environment?.violationType;
    
    if (!contractName || !violationType || !failure.location) {
      return actions;
    }

    switch (violationType) {
      case 'input':
        actions.push(...await this.fixInputViolation(failure, contractName));
        break;
      case 'output':
        actions.push(...await this.fixOutputViolation(failure, contractName));
        break;
      case 'schema':
        actions.push(...await this.fixSchemaViolation(failure, contractName));
        break;
    }

    return actions.filter(action => this.validateRepairAction(action));
  }

  private async fixInputViolation(
    failure: FailureArtifact,
    contractName: string
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    const actualData = this.extractActualData(failure);
    
    if (!actualData) return actions;

    // Generate Zod schema from actual data
    const zodSchema = this.generateZodSchema(actualData, contractName);
    
    actions.push(this.createValidationUpdateAction(
      `Update ${contractName} input schema to accept actual data structure`,
      filePath,
      '// Old schema placeholder',
      zodSchema,
      0.8
    ));

    // Add data transformation if needed
    const transformation = this.generateDataTransformation(actualData);
    if (transformation) {
      actions.push(this.createCodeChangeAction(
        `Add data transformation for ${contractName} input`,
        filePath,
        '// Add transformation here',
        transformation,
        failure.location!.startLine,
        failure.location!.endLine,
        0.7,
        2
      ));
    }

    // Add optional field handling
    const optionalFields = this.identifyOptionalFields(actualData);
    if (optionalFields.length > 0) {
      actions.push(this.createValidationUpdateAction(
        `Make fields optional in ${contractName}: ${optionalFields.join(', ')}`,
        filePath,
        '// Update schema with optional fields',
        this.generateOptionalFieldsSchema(optionalFields),
        0.9
      ));
    }

    return actions;
  }

  private async fixOutputViolation(
    failure: FailureArtifact,
    contractName: string
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    const actualData = this.extractActualData(failure);
    
    if (!actualData) return actions;

    // Fix output schema to match actual output
    const outputSchema = this.generateZodSchema(actualData, `${contractName}Output`);
    
    actions.push(this.createValidationUpdateAction(
      `Update ${contractName} output schema to match actual output`,
      filePath,
      '// Old output schema',
      outputSchema,
      0.8
    ));

    // Add output transformation
    const outputTransformation = this.generateOutputTransformation(actualData);
    if (outputTransformation) {
      actions.push(this.createCodeChangeAction(
        `Add output transformation for ${contractName}`,
        filePath,
        '// Add output transformation',
        outputTransformation,
        failure.location!.startLine,
        failure.location!.endLine,
        0.7,
        2
      ));
    }

    return actions;
  }

  private async fixSchemaViolation(
    failure: FailureArtifact,
    contractName: string
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    const actualData = this.extractActualData(failure);
    
    if (!actualData) return actions;

    // Generate comprehensive schema update
    const schemaUpdate = this.generateSchemaUpdate(actualData, contractName);
    
    actions.push(this.createValidationUpdateAction(
      `Comprehensive schema update for ${contractName}`,
      filePath,
      '// Current schema',
      schemaUpdate,
      0.7
    ));

    // Add schema versioning
    const versionedSchema = this.generateVersionedSchema(actualData, contractName);
    actions.push(this.createValidationUpdateAction(
      `Add versioned schema for backward compatibility`,
      filePath,
      '// Add versioned schema',
      versionedSchema,
      0.6
    ));

    return actions;
  }

  private extractActualData(failure: FailureArtifact): any {
    try {
      // Try to extract actual data from logs
      const dataLog = failure.evidence.logs.find(log => 
        log.includes('Actual data:')
      );
      
      if (dataLog) {
        const jsonMatch = dataLog.match(/Actual data:\s*(.+)/);
        if (jsonMatch) {
          return JSON.parse(jsonMatch[1]);
        }
      }
      
      return null;
    } catch (error) {
      return null;
    }
  }

  private generateZodSchema(data: any, schemaName: string): string {
    const schemaLines = [`export const ${schemaName}Schema = z.object({`];
    
    if (typeof data === 'object' && data !== null) {
      for (const [key, value] of Object.entries(data)) {
        const zodType = this.inferZodType(value);
        schemaLines.push(`  ${key}: ${zodType},`);
      }
    }
    
    schemaLines.push('});');
    schemaLines.push('');
    schemaLines.push(`export type ${schemaName} = z.infer<typeof ${schemaName}Schema>;`);
    
    return schemaLines.join('\n');
  }

  private inferZodType(value: any): string {
    if (value === null || value === undefined) {
      return 'z.string().optional()';
    }
    
    if (typeof value === 'string') {
      if (value.match(/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}/)) {
        return 'z.string().datetime()';
      }
      if (value.includes('@')) {
        return 'z.string().email()';
      }
      if (value.match(/^https?:\/\//)) {
        return 'z.string().url()';
      }
      return 'z.string()';
    }
    
    if (typeof value === 'number') {
      return Number.isInteger(value) ? 'z.number().int()' : 'z.number()';
    }
    
    if (typeof value === 'boolean') {
      return 'z.boolean()';
    }
    
    if (Array.isArray(value)) {
      if (value.length === 0) {
        return 'z.array(z.any())';
      }
      const firstElementType = this.inferZodType(value[0]);
      return `z.array(${firstElementType})`;
    }
    
    if (typeof value === 'object') {
      return 'z.record(z.any())';
    }
    
    return 'z.any()';
  }

  private generateDataTransformation(data: any): string | null {
    const transformations: string[] = [];
    
    if (typeof data === 'object' && data !== null) {
      for (const [key, value] of Object.entries(data)) {
        // Add common transformations
        if (typeof value === 'string' && !isNaN(Date.parse(value))) {
          transformations.push(`  ${key}: new Date(input.${key}).toISOString(),`);
        } else if (typeof value === 'string' && !isNaN(Number(value))) {
          transformations.push(`  ${key}: Number(input.${key}),`);
        } else if (value === null || value === undefined) {
          transformations.push(`  ${key}: input.${key} ?? undefined,`);
        }
      }
    }
    
    if (transformations.length === 0) return null;
    
    return [
      'function transformInput(input: any) {',
      '  return {',
      '    ...input,',
      ...transformations,
      '  };',
      '}'
    ].join('\n');
  }

  private generateOutputTransformation(data: any): string | null {
    const transformations: string[] = [];
    
    if (typeof data === 'object' && data !== null) {
      for (const [key, value] of Object.entries(data)) {
        if (key.endsWith('At') && typeof value === 'string') {
          transformations.push(`  ${key}: output.${key} ? new Date(output.${key}).toISOString() : undefined,`);
        }
      }
    }
    
    if (transformations.length === 0) return null;
    
    return [
      'function transformOutput(output: any) {',
      '  return {',
      '    ...output,',
      ...transformations,
      '  };',
      '}'
    ].join('\n');
  }

  private identifyOptionalFields(data: any): string[] {
    const optionalFields: string[] = [];
    
    if (typeof data === 'object' && data !== null) {
      for (const [key, value] of Object.entries(data)) {
        if (value === null || value === undefined || value === '') {
          optionalFields.push(key);
        }
      }
    }
    
    return optionalFields;
  }

  private generateOptionalFieldsSchema(fields: string[]): string {
    const updates = fields.map(field => 
      `// Make ${field} optional\n${field}: ${field}.optional(),`
    );
    
    return updates.join('\n');
  }

  private generateSchemaUpdate(data: any, contractName: string): string {
    const baseSchema = this.generateZodSchema(data, contractName);
    
    const enhancements = [
      '// Enhanced schema with runtime validation',
      '.refine((data) => {',
      '  // Add custom validation logic here',
      '  return true;',
      '}, {',
      '  message: "Custom validation failed"',
      '})',
      '.transform((data) => {',
      '  // Add data transformation here',
      '  return data;',
      '})'
    ];
    
    return baseSchema + '\n' + enhancements.join('\n');
  }

  private generateVersionedSchema(data: any, contractName: string): string {
    return [
      `// Versioned schema for ${contractName}`,
      `export const ${contractName}SchemaV1 = ${contractName}Schema;`,
      '',
      `export const ${contractName}SchemaV2 = z.object({`,
      '  version: z.literal("2.0").default("2.0"),',
      '  data: ' + contractName + 'SchemaV1,',
      '  metadata: z.object({',
      '    timestamp: z.string().datetime(),',
      '    source: z.string().default("api")',
      '  }).optional()',
      '});',
      '',
      `export function migrate${contractName}(data: any): any {`,
      '  if (data.version === "2.0") return data;',
      '  return {',
      '    version: "2.0",',
      '    data,',
      '    metadata: {',
      '      timestamp: new Date().toISOString(),',
      '      source: "migration"',
      '    }',
      '  };',
      '}'
    ].join('\n');
  }
}