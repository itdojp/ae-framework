/**
 * Deterministic Code Generator
 * Ensures consistent code generation from AE-IR specifications
 */

import { createHash } from 'crypto';
import { readFileSync, writeFileSync, existsSync, mkdirSync } from 'fs';
import { dirname, join, relative } from 'path';
import { AEIR } from '@ae-framework/spec-compiler';

export interface CodegenOptions {
  /** Input AE-IR file path */
  inputPath: string;
  /** Output directory for generated code */
  outputDir: string;
  /** Template directory */
  templateDir?: string;
  /** Target language/framework */
  target: 'typescript' | 'react' | 'api' | 'database';
  /** Enable drift detection */
  enableDriftDetection?: boolean;
  /** Custom hash algorithm */
  hashAlgorithm?: 'sha256' | 'md5';
  /** Preserve existing manual modifications */
  preserveManualChanges?: boolean;
}

export interface GeneratedFile {
  /** Relative file path */
  filePath: string;
  /** Generated content */
  content: string;
  /** Content hash for drift detection */
  hash: string;
  /** Generation timestamp */
  timestamp: string;
  /** Source specification hash */
  specHash: string;
}

export interface DriftDetectionResult {
  /** Whether drift was detected */
  hasDrift: boolean;
  /** Files with detected drift */
  driftedFiles: Array<{
    filePath: string;
    reason: 'spec_changed' | 'manual_modification' | 'template_changed';
    expectedHash: string;
    actualHash: string;
    lastGenerated: string;
  }>;
  /** Summary of drift analysis */
  summary: {
    totalFiles: number;
    driftedFiles: number;
    upToDateFiles: number;
  };
}

export interface CodegenManifest {
  /** Generation metadata */
  metadata: {
    generatedAt: string;
    specHash: string;
    templateHash: string;
    options: CodegenOptions;
  };
  /** Generated files registry */
  files: GeneratedFile[];
}

export class DeterministicCodeGenerator {
  private options: CodegenOptions;
  private manifestPath: string;

  constructor(options: CodegenOptions) {
    this.options = {
      hashAlgorithm: 'sha256',
      enableDriftDetection: true,
      preserveManualChanges: true,
      ...options,
    };
    this.manifestPath = join(this.options.outputDir, '.codegen-manifest.json');
  }

  /**
   * Generate code from AE-IR specification
   */
  async generate(): Promise<CodegenManifest> {
    // Load and validate AE-IR
    const ir = this.loadAEIR();
    const specHash = this.calculateHash(JSON.stringify(ir, null, 2));

    // Perform drift detection if enabled
    if (this.options.enableDriftDetection) {
      const driftResult = await this.detectDrift(specHash);
      if (driftResult.hasDrift) {
        console.warn('⚠️  Drift detected:', driftResult.summary);
        if (!this.options.preserveManualChanges) {
          throw new Error('Drift detected and preserveManualChanges is false');
        }
      }
    }

    // Generate code based on target
    const generatedFiles = await this.generateFiles(ir, specHash);

    // Create manifest
    const manifest: CodegenManifest = {
      metadata: {
        generatedAt: new Date().toISOString(),
        specHash,
        templateHash: this.calculateTemplateHash(),
        options: this.options,
      },
      files: generatedFiles,
    };

    // Write manifest
    this.writeManifest(manifest);

    return manifest;
  }

  /**
   * Detect drift between current state and expected state
   */
  async detectDrift(currentSpecHash: string): Promise<DriftDetectionResult> {
    if (!existsSync(this.manifestPath)) {
      return {
        hasDrift: false,
        driftedFiles: [],
        summary: { totalFiles: 0, driftedFiles: 0, upToDateFiles: 0 },
      };
    }

    const manifest = this.loadManifest();
    const driftedFiles: DriftDetectionResult['driftedFiles'] = [];

    // Check spec changes
    if (manifest.metadata.specHash !== currentSpecHash) {
      // All files are potentially drifted due to spec changes
      for (const file of manifest.files) {
        const filePath = join(this.options.outputDir, file.filePath);
        if (existsSync(filePath)) {
          const currentContent = readFileSync(filePath, 'utf-8');
          const currentHash = this.calculateHash(currentContent);
          
          if (currentHash !== file.hash) {
            driftedFiles.push({
              filePath: file.filePath,
              reason: 'spec_changed',
              expectedHash: file.hash,
              actualHash: currentHash,
              lastGenerated: file.timestamp,
            });
          }
        }
      }
    } else {
      // Check individual file modifications
      for (const file of manifest.files) {
        const filePath = join(this.options.outputDir, file.filePath);
        if (existsSync(filePath)) {
          const currentContent = readFileSync(filePath, 'utf-8');
          const currentHash = this.calculateHash(currentContent);
          
          if (currentHash !== file.hash) {
            driftedFiles.push({
              filePath: file.filePath,
              reason: 'manual_modification',
              expectedHash: file.hash,
              actualHash: currentHash,
              lastGenerated: file.timestamp,
            });
          }
        }
      }
    }

    return {
      hasDrift: driftedFiles.length > 0,
      driftedFiles,
      summary: {
        totalFiles: manifest.files.length,
        driftedFiles: driftedFiles.length,
        upToDateFiles: manifest.files.length - driftedFiles.length,
      },
    };
  }

  /**
   * Generate files based on target and AE-IR
   */
  private async generateFiles(ir: AEIR, specHash: string): Promise<GeneratedFile[]> {
    const files: GeneratedFile[] = [];
    const timestamp = new Date().toISOString();

    switch (this.options.target) {
      case 'typescript':
        files.push(...await this.generateTypeScriptFiles(ir, specHash, timestamp));
        break;
      case 'react':
        files.push(...await this.generateReactFiles(ir, specHash, timestamp));
        break;
      case 'api':
        files.push(...await this.generateAPIFiles(ir, specHash, timestamp));
        break;
      case 'database':
        files.push(...await this.generateDatabaseFiles(ir, specHash, timestamp));
        break;
    }

    // Write generated files
    for (const file of files) {
      const fullPath = join(this.options.outputDir, file.filePath);
      mkdirSync(dirname(fullPath), { recursive: true });
      writeFileSync(fullPath, file.content, 'utf-8');
    }

    return files;
  }

  /**
   * Generate TypeScript types and interfaces
   */
  private async generateTypeScriptFiles(ir: AEIR, specHash: string, timestamp: string): Promise<GeneratedFile[]> {
    const files: GeneratedFile[] = [];

    // Generate domain types
    const typesContent = this.generateTypeScriptTypes(ir);
    files.push({
      filePath: 'types/domain.ts',
      content: typesContent,
      hash: this.calculateHash(typesContent),
      timestamp,
      specHash,
    });

    // Generate API interfaces
    if (ir.api.length > 0) {
      const apiContent = this.generateAPIInterfaces(ir);
      files.push({
        filePath: 'types/api.ts',
        content: apiContent,
        hash: this.calculateHash(apiContent),
        timestamp,
        specHash,
      });
    }

    // Generate validation schemas
    const validationContent = this.generateValidationSchemas(ir);
    files.push({
      filePath: 'schemas/validation.ts',
      content: validationContent,
      hash: this.calculateHash(validationContent),
      timestamp,
      specHash,
    });

    return files;
  }

  /**
   * Generate React components
   */
  private async generateReactFiles(ir: AEIR, specHash: string, timestamp: string): Promise<GeneratedFile[]> {
    const files: GeneratedFile[] = [];

    for (const entity of ir.domain) {
      // Generate entity form component
      const formContent = this.generateEntityForm(entity);
      files.push({
        filePath: `components/${entity.name}Form.tsx`,
        content: formContent,
        hash: this.calculateHash(formContent),
        timestamp,
        specHash,
      });

      // Generate entity list component
      const listContent = this.generateEntityList(entity);
      files.push({
        filePath: `components/${entity.name}List.tsx`,
        content: listContent,
        hash: this.calculateHash(listContent),
        timestamp,
        specHash,
      });
    }

    return files;
  }

  /**
   * Generate API handlers
   */
  private async generateAPIFiles(ir: AEIR, specHash: string, timestamp: string): Promise<GeneratedFile[]> {
    const files: GeneratedFile[] = [];

    for (const api of ir.api) {
      const handlerContent = this.generateAPIHandler(api);
      const fileName = `handlers/${api.path.replace(/[^a-zA-Z0-9]/g, '_')}_${api.method.toLowerCase()}.ts`;
      files.push({
        filePath: fileName,
        content: handlerContent,
        hash: this.calculateHash(handlerContent),
        timestamp,
        specHash,
      });
    }

    return files;
  }

  /**
   * Generate database schemas
   */
  private async generateDatabaseFiles(ir: AEIR, specHash: string, timestamp: string): Promise<GeneratedFile[]> {
    const files: GeneratedFile[] = [];

    // Generate SQL migrations
    const migrationContent = this.generateSQLMigration(ir);
    files.push({
      filePath: 'migrations/001_initial_schema.sql',
      content: migrationContent,
      hash: this.calculateHash(migrationContent),
      timestamp,
      specHash,
    });

    // Generate ORM models
    for (const entity of ir.domain) {
      const modelContent = this.generateORMModel(entity);
      files.push({
        filePath: `models/${entity.name}.ts`,
        content: modelContent,
        hash: this.calculateHash(modelContent),
        timestamp,
        specHash,
      });
    }

    return files;
  }

  /**
   * Helper methods for code generation
   */
  private generateTypeScriptTypes(ir: AEIR): string {
    return `// Generated from AE-IR specification
// DO NOT MODIFY - This file is automatically generated

${ir.domain.map(entity => `
export interface ${entity.name} {
${entity.fields.map(field => 
  `  ${field.name}${field.required ? '' : '?'}: ${this.mapTypeToTS(field.type)};`
).join('\n')}
}
`).join('\n')}

export type DomainEntities = ${ir.domain.map(e => e.name).join(' | ')};
`;
  }

  private generateAPIInterfaces(ir: AEIR): string {
    return `// Generated API interfaces
// DO NOT MODIFY - This file is automatically generated

${ir.api.map(api => `
export interface ${api.method}${api.path.replace(/[^a-zA-Z0-9]/g, '')}Request {
  // Add request parameters based on API definition
}

export interface ${api.method}${api.path.replace(/[^a-zA-Z0-9]/g, '')}Response {
  // Add response structure based on API definition
}
`).join('\n')}
`;
  }

  private generateValidationSchemas(ir: AEIR): string {
    return `// Generated validation schemas
// DO NOT MODIFY - This file is automatically generated

import { z } from 'zod';

${ir.domain.map(entity => `
export const ${entity.name}Schema = z.object({
${entity.fields.map(field => 
  `  ${field.name}: z.${this.mapTypeToZod(field.type)}()${field.required ? '' : '.optional()'},`
).join('\n')}
});
`).join('\n')}
`;
  }

  private generateEntityForm(entity: any): string {
    return `// Generated ${entity.name} form component
// DO NOT MODIFY - This file is automatically generated

import React from 'react';

export interface ${entity.name}FormProps {
  onSubmit: (data: ${entity.name}) => void;
  initialData?: Partial<${entity.name}>;
}

export const ${entity.name}Form: React.FC<${entity.name}FormProps> = ({
  onSubmit,
  initialData = {},
}) => {
  return (
    <form>
      {/* Generated form fields */}
${entity.fields.map((field: any) => `      <div>
        <label>${field.name}</label>
        <input type="${this.mapTypeToInputType(field.type)}" name="${field.name}" />
      </div>`).join('\n')}
      <button type="submit">Submit</button>
    </form>
  );
};
`;
  }

  private generateEntityList(entity: any): string {
    return `// Generated ${entity.name} list component
// DO NOT MODIFY - This file is automatically generated

import React from 'react';

export interface ${entity.name}ListProps {
  items: ${entity.name}[];
  onEdit?: (item: ${entity.name}) => void;
  onDelete?: (id: string) => void;
}

export const ${entity.name}List: React.FC<${entity.name}ListProps> = ({
  items,
  onEdit,
  onDelete,
}) => {
  return (
    <div>
      {items.map(item => (
        <div key={item.id}>
          {/* Generated item display */}
${entity.fields.slice(0, 3).map((field: any) => `          <span>{item.${field.name}}</span>`).join('\n')}
          {onEdit && <button onClick={() => onEdit(item)}>Edit</button>}
          {onDelete && <button onClick={() => onDelete(item.id)}>Delete</button>}
        </div>
      ))}
    </div>
  );
};
`;
  }

  private generateAPIHandler(api: any): string {
    return `// Generated API handler for ${api.method} ${api.path}
// DO NOT MODIFY - This file is automatically generated

import { Request, Response } from 'express';

export const handle${api.method}${api.path.replace(/[^a-zA-Z0-9]/g, '')} = async (
  req: Request,
  res: Response
) => {
  try {
    // Generated handler logic
    res.json({ message: 'Handler not implemented' });
  } catch (error) {
    res.status(500).json({ error: 'Internal server error' });
  }
};
`;
  }

  private generateSQLMigration(ir: AEIR): string {
    return `-- Generated SQL migration
-- DO NOT MODIFY - This file is automatically generated

${ir.domain.map(entity => `
CREATE TABLE ${entity.name.toLowerCase()}s (
${entity.fields.map(field => 
  `  ${field.name} ${this.mapTypeToSQL(field.type)}${field.required ? ' NOT NULL' : ''},`
).join('\n')}
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP
);
`).join('\n')}
`;
  }

  private generateORMModel(entity: any): string {
    return `// Generated ORM model for ${entity.name}
// DO NOT MODIFY - This file is automatically generated

import { Entity, PrimaryGeneratedColumn, Column, CreateDateColumn, UpdateDateColumn } from 'typeorm';

@Entity('${entity.name.toLowerCase()}s')
export class ${entity.name} {
  @PrimaryGeneratedColumn('uuid')
  id: string;

${entity.fields.filter((f: any) => f.name !== 'id').map((field: any) => `
  @Column(${this.getColumnOptions(field)})
  ${field.name}: ${this.mapTypeToTS(field.type)};`).join('')}

  @CreateDateColumn()
  createdAt: Date;

  @UpdateDateColumn()
  updatedAt: Date;
}
`;
  }

  /**
   * Helper methods for type mapping
   */
  private mapTypeToTS(type: string): string {
    const typeMap: Record<string, string> = {
      'string': 'string',
      'UUID': 'string',
      'integer': 'number',
      'decimal': 'number',
      'boolean': 'boolean',
      'datetime': 'Date',
      'text': 'string',
      'enum': 'string', // Simplified
    };
    return typeMap[type] || 'string';
  }

  private mapTypeToZod(type: string): string {
    const typeMap: Record<string, string> = {
      'string': 'string',
      'UUID': 'string',
      'integer': 'number',
      'decimal': 'number',
      'boolean': 'boolean',
      'datetime': 'date',
      'text': 'string',
      'enum': 'string',
    };
    return typeMap[type] || 'string';
  }

  private mapTypeToInputType(type: string): string {
    const typeMap: Record<string, string> = {
      'string': 'text',
      'UUID': 'text',
      'integer': 'number',
      'decimal': 'number',
      'boolean': 'checkbox',
      'datetime': 'datetime-local',
      'text': 'textarea',
      'enum': 'select',
    };
    return typeMap[type] || 'text';
  }

  private mapTypeToSQL(type: string): string {
    const typeMap: Record<string, string> = {
      'string': 'VARCHAR(255)',
      'UUID': 'UUID',
      'integer': 'INTEGER',
      'decimal': 'DECIMAL(10,2)',
      'boolean': 'BOOLEAN',
      'datetime': 'TIMESTAMP',
      'text': 'TEXT',
      'enum': 'VARCHAR(50)',
    };
    return typeMap[type] || 'VARCHAR(255)';
  }

  private getColumnOptions(field: any): string {
    const options: string[] = [];
    if (field.type === 'text') options.push('{ type: "text" }');
    if (!field.required) options.push('{ nullable: true }');
    return options.length > 0 ? options.join(', ') : '';
  }

  /**
   * Utility methods
   */
  private loadAEIR(): AEIR {
    if (!existsSync(this.options.inputPath)) {
      throw new Error(`AE-IR file not found: ${this.options.inputPath}`);
    }
    
    const content = readFileSync(this.options.inputPath, 'utf-8');
    return JSON.parse(content);
  }

  private loadManifest(): CodegenManifest {
    const content = readFileSync(this.manifestPath, 'utf-8');
    return JSON.parse(content);
  }

  private writeManifest(manifest: CodegenManifest): void {
    mkdirSync(dirname(this.manifestPath), { recursive: true });
    writeFileSync(this.manifestPath, JSON.stringify(manifest, null, 2), 'utf-8');
  }

  private calculateHash(content: string): string {
    return createHash(this.options.hashAlgorithm!).update(content).digest('hex');
  }

  private calculateTemplateHash(): string {
    // Calculate hash of template files if templateDir is provided
    if (this.options.templateDir && existsSync(this.options.templateDir)) {
      // Simplified - in practice, would hash all template files
      return this.calculateHash(this.options.templateDir);
    }
    return 'no-template';
  }
}