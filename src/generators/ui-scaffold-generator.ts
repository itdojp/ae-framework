import * as fs from 'fs';
import * as path from 'path';
import Handlebars from 'handlebars';
import { Phase6Telemetry } from '../telemetry/phase6-metrics.js';

interface PhaseState {
  entities: Record<string, EntityDefinition>;
  ui_preferences?: UIPreferences;
  relationships?: Record<string, any>;
}

interface EntityDefinition {
  description: string;
  attributes: Record<string, AttributeDefinition>;
  constraints?: any;
  acceptance_criteria?: string[];
}

interface AttributeDefinition {
  type: string;
  required: boolean;
  validation?: string;
  description: string;
  default?: any;
}

interface UIPreferences {
  theme?: string;
  layout?: string;
  components?: string;
  styling?: string;
  forms?: string;
  validation?: string;
  data_fetching?: string;
  testing?: string;
}

interface GeneratorOptions {
  outputDir: string;
  dryRun?: boolean;
  overwrite?: boolean;
  targetEntity?: string;
}

interface GenerationResult {
  success: boolean;
  files: string[];
  error?: string;
}

export class UIScaffoldGenerator {
  private phaseState: PhaseState;
  private options: GeneratorOptions;
  private templatesDir: string;

  constructor(phaseState: PhaseState, options: GeneratorOptions) {
    this.phaseState = phaseState;
    this.options = options;
    // Find ae-framework root directory
    const currentDir = process.cwd();
    const frameworkRoot = this.findFrameworkRoot(currentDir);
    this.templatesDir = path.join(frameworkRoot, 'templates', 'ui');
    
    this.registerHandlebarsHelpers();
  }

  private findFrameworkRoot(startDir: string): string {
    let currentDir = startDir;
    
    while (currentDir !== path.dirname(currentDir)) {
      // Check if this directory contains package.json with ae-framework
      const packagePath = path.join(currentDir, 'package.json');
      if (fs.existsSync(packagePath)) {
        try {
          const packageContent = JSON.parse(fs.readFileSync(packagePath, 'utf8'));
          if (packageContent.name === 'ae-framework') {
            return currentDir;
          }
        } catch (error) {
          // Continue searching
        }
      }
      
      // Check if templates directory exists here
      const templatesPath = path.join(currentDir, 'templates', 'ui');
      if (fs.existsSync(templatesPath)) {
        return currentDir;
      }
      
      currentDir = path.dirname(currentDir);
    }
    
    // Fallback to current working directory
    return process.cwd();
  }

  async generateAll(): Promise<Record<string, GenerationResult>> {
    return await Phase6Telemetry.instrumentScaffoldOperation(
      'generate_all_entities',
      async () => {
        const results: Record<string, GenerationResult> = {};
        const entities = this.options.targetEntity 
          ? { [this.options.targetEntity]: this.phaseState.entities[this.options.targetEntity] }
          : this.phaseState.entities;

    for (const [entityName, entityDef] of Object.entries(entities)) {
      if (!entityDef) {
        results[entityName] = {
          success: false,
          files: [],
          error: `Entity ${entityName} not found in phase state`
        };
        continue;
      }

      try {
        const files = await this.generateEntityUI(entityName, entityDef);
        results[entityName] = {
          success: true,
          files
        };
      } catch (error) {
        results[entityName] = {
          success: false,
          files: [],
          error: error instanceof Error ? error.message : String(error)
        };
      }
    }

        return results;
      },
      {
        entity_count: Object.keys(this.options.targetEntity 
          ? { [this.options.targetEntity]: this.phaseState.entities[this.options.targetEntity] }
          : this.phaseState.entities).length,
        target_entity: this.options.targetEntity || 'all',
        output_dir: this.options.outputDir,
      }
    );
  }

  private async generateEntityUI(entityName: string, entityDef: EntityDefinition): Promise<string[]> {
    const generatedFiles: string[] = [];
    const context = this.buildTemplateContext(entityName, entityDef);

    const templates = [
      { template: 'page-list.tsx.template', output: `apps/web/app/${context.entityName}/page.tsx` },
      { template: 'page-new.tsx.template', output: `apps/web/app/${context.entityName}/new/page.tsx` },
      { template: 'page-detail.tsx.template', output: `apps/web/app/${context.entityName}/[id]/page.tsx` },
      { template: 'component-form.tsx.template', output: `apps/web/components/${context.EntityName}Form.tsx` },
      { template: 'component-card.tsx.template', output: `apps/web/components/${context.EntityName}Card.tsx` },
      { template: 'story.stories.tsx.template', output: `apps/storybook/stories/${context.EntityName}.stories.tsx` },
      { template: 'e2e.spec.ts.template', output: `apps/web/__e2e__/${context.entityName}.spec.ts` }
    ];

    for (const { template, output } of templates) {
      const outputPath = path.join(this.options.outputDir, output);
      
      if (!this.options.dryRun) {
        if (fs.existsSync(outputPath) && !this.options.overwrite) {
          console.warn(`Skipping existing file: ${outputPath}`);
          continue;
        }

        const content = await this.renderTemplate(template, context);
        await this.writeFile(outputPath, content);
      }
      
      generatedFiles.push(output);
    }

    return generatedFiles;
  }

  private buildTemplateContext(entityName: string, entityDef: EntityDefinition): any {
    const attributes = entityDef.attributes;
    const entityNameLower = entityName.toLowerCase();
    
    // Find key fields
    const displayNameField = this.findDisplayNameField(attributes);
    const descriptionField = this.findDescriptionField(attributes);
    const statusField = this.findStatusField(attributes);
    
    // Categorize attributes
    const editableAttributes = this.getEditableAttributes(attributes);
    const displayAttributes = this.getDisplayAttributes(attributes);
    const cardDisplayFields = this.getCardDisplayFields(attributes);
    const timestampFields = this.getTimestampFields(attributes);
    const requiredFormFields = this.getRequiredFormFields(editableAttributes);
    const optionalFormFields = this.getOptionalFormFields(editableAttributes);

    return {
      EntityName: entityName,
      entityName: entityNameLower,
      description: entityDef.description,
      attributes,
      editableAttributes,
      displayAttributes,
      cardDisplayFields,
      timestampFields,
      requiredFormFields,
      optionalFormFields,
      editableFormFields: editableAttributes,
      displayNameField,
      descriptionField,
      statusField,
      hasStatusField: !!statusField,
      statusOptions: statusField ? this.getEnumOptions(attributes[statusField]?.validation) : [],
      acceptanceCriteria: entityDef.acceptance_criteria || []
    };
  }

  private findDisplayNameField(attributes: Record<string, AttributeDefinition>): string | null {
    const candidates = ['name', 'title', 'label', 'displayName'];
    for (const candidate of candidates) {
      if (attributes[candidate] && attributes[candidate].type === 'string') {
        return candidate;
      }
    }
    return null;
  }

  private findDescriptionField(attributes: Record<string, AttributeDefinition>): string | null {
    const candidates = ['description', 'summary', 'notes'];
    for (const candidate of candidates) {
      if (attributes[candidate] && attributes[candidate].type === 'string') {
        return candidate;
      }
    }
    return null;
  }

  private findStatusField(attributes: Record<string, AttributeDefinition>): string | null {
    const candidates = ['status', 'state', 'active'];
    for (const candidate of candidates) {
      if (attributes[candidate] && (
        attributes[candidate].validation?.includes('enum') || 
        attributes[candidate].type === 'boolean'
      )) {
        return candidate;
      }
    }
    return null;
  }

  private getEditableAttributes(attributes: Record<string, AttributeDefinition>): Record<string, AttributeDefinition> {
    const editable: Record<string, AttributeDefinition> = {};
    const excludeFields = ['id', 'createdAt', 'updatedAt'];
    
    for (const [key, attr] of Object.entries(attributes)) {
      if (!excludeFields.includes(key)) {
        editable[key] = attr;
      }
    }
    
    return editable;
  }

  private getDisplayAttributes(attributes: Record<string, AttributeDefinition>): Record<string, AttributeDefinition> {
    // For detail view - show most attributes except internal ones
    const display: Record<string, AttributeDefinition> = {};
    const excludeFields = ['id'];
    
    for (const [key, attr] of Object.entries(attributes)) {
      if (!excludeFields.includes(key)) {
        display[key] = attr;
      }
    }
    
    return display;
  }

  private getCardDisplayFields(attributes: Record<string, AttributeDefinition>): Record<string, AttributeDefinition> {
    // For cards - show key fields only
    const display: Record<string, AttributeDefinition> = {};
    const priorityFields = ['price', 'status', 'category', 'total', 'stock'];
    
    let count = 0;
    for (const field of priorityFields) {
      if (attributes[field] && count < 3) {
        display[field] = attributes[field];
        count++;
      }
    }
    
    return display;
  }

  private getTimestampFields(attributes: Record<string, AttributeDefinition>): Record<string, AttributeDefinition> {
    const timestamps: Record<string, AttributeDefinition> = {};
    
    for (const [key, attr] of Object.entries(attributes)) {
      if (attr.type === 'date' && (key.includes('At') || key.includes('Date'))) {
        timestamps[key] = attr;
      }
    }
    
    return timestamps;
  }

  private getRequiredFormFields(attributes: Record<string, AttributeDefinition>): Record<string, AttributeDefinition> {
    const required: Record<string, AttributeDefinition> = {};
    
    for (const [key, attr] of Object.entries(attributes)) {
      if (attr.required) {
        required[key] = attr;
      }
    }
    
    return required;
  }

  private getOptionalFormFields(attributes: Record<string, AttributeDefinition>): Record<string, AttributeDefinition> {
    const optional: Record<string, AttributeDefinition> = {};
    
    for (const [key, attr] of Object.entries(attributes)) {
      if (!attr.required) {
        optional[key] = attr;
      }
    }
    
    return optional;
  }

  private getEnumOptions(validation?: string): string[] {
    if (!validation?.includes('enum:')) return [];
    
    const enumMatch = validation.match(/enum:([^,]+)/);
    if (!enumMatch) return [];
    const group = enumMatch[1] ?? '';
    if (!group) return [];
    return group.split('|').map(s => s.trim());
  }

  private async renderTemplate(templateName: string, context: any): Promise<string> {
    const templatePath = path.join(this.templatesDir, templateName);
    
    if (!fs.existsSync(templatePath)) {
      throw new Error(`Template not found: ${templatePath}`);
    }
    
    const templateContent = fs.readFileSync(templatePath, 'utf8');
    const template = Handlebars.compile(templateContent);
    
    return template(context);
  }

  private async writeFile(filePath: string, content: string): Promise<void> {
    const dir = path.dirname(filePath);
    
    // Create directories if they don't exist
    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
    }
    
    fs.writeFileSync(filePath, content, 'utf8');
  }

  public validatePhaseState(): { valid: boolean; errors: string[]; entityCount: number; uiFramework: string } {
    const errors: string[] = [];
    
    if (!this.phaseState.entities) {
      errors.push('No entities found in phase state');
    }
    
    const entityCount = Object.keys(this.phaseState.entities || {}).length;
    if (entityCount === 0) {
      errors.push('Phase state contains no entities');
    }
    
    // Validate each entity
    for (const [entityName, entityDef] of Object.entries(this.phaseState.entities || {})) {
      if (!entityDef.attributes) {
        errors.push(`Entity ${entityName} has no attributes`);
      }
      
      if (Object.keys(entityDef.attributes || {}).length === 0) {
        errors.push(`Entity ${entityName} has no attributes defined`);
      }
    }
    
    const uiFramework = this.phaseState.ui_preferences?.components || 'default';
    
    return {
      valid: errors.length === 0,
      errors,
      entityCount,
      uiFramework
    };
  }

  private registerHandlebarsHelpers(): void {
    // Helper to get TypeScript type from attribute type
    Handlebars.registerHelper('getTypeScriptType', (type: string) => {
      switch (type) {
        case 'string': return 'string';
        case 'number': return 'number';
        case 'boolean': return 'boolean';
        case 'date': return 'string'; // ISO string
        case 'array': return 'any[]';
        case 'object': return 'any';
        default: return 'any';
      }
    });

    // Helper to get Zod schema from attribute
    Handlebars.registerHelper('getZodSchema', (attr: AttributeDefinition) => {
      let schema = '';
      
      switch (attr.type) {
        case 'string':
          schema = 'z.string()';
          if (attr.validation?.includes('min:')) {
            const min = attr.validation.match(/min:(\d+)/)?.[1];
            if (min) schema += `.min(${min})`;
          }
          if (attr.validation?.includes('max:')) {
            const max = attr.validation.match(/max:(\d+)/)?.[1];
            if (max) schema += `.max(${max})`;
          }
          if (attr.validation?.includes('enum:')) {
            const enumMatch = attr.validation.match(/enum:([^,]+)/);
            if (enumMatch) {
              const group = enumMatch[1] ?? '';
              const options = group ? group.split('|').map(s => `"${s.trim()}"`).join(', ') : '';
              schema = options ? `z.enum([${options}])` : 'z.string()';
            }
          }
          break;
        case 'number':
          schema = 'z.number()';
          if (attr.validation?.includes('min:')) {
            const min = attr.validation.match(/min:(\d+)/)?.[1];
            if (min) schema += `.min(${min})`;
          }
          if (attr.validation?.includes('integer')) {
            schema += '.int()';
          }
          break;
        case 'boolean':
          schema = 'z.boolean()';
          break;
        case 'date':
          schema = 'z.string().datetime()';
          break;
        case 'array':
          schema = 'z.array(z.any())';
          if (attr.validation?.includes('min_length:')) {
            const min = attr.validation.match(/min_length:(\d+)/)?.[1];
            if (min) schema += `.min(${min})`;
          }
          break;
        default:
          schema = 'z.any()';
      }
      
      if (!attr.required) {
        schema += '.optional()';
      }
      
      return schema;
    });

    // Other helpers
    Handlebars.registerHelper('getFieldLabel', (key: string) => {
      return key.charAt(0).toUpperCase() + key.slice(1).replace(/([A-Z])/g, ' $1');
    });

    Handlebars.registerHelper('getFieldPlaceholder', (key: string, description: string) => {
      return description || `Enter ${key.toLowerCase()}`;
    });

    Handlebars.registerHelper('capitalize', (str: string) => {
      return str.charAt(0).toUpperCase() + str.slice(1);
    });

    Handlebars.registerHelper('getInputType', (type: string) => {
      switch (type) {
        case 'number': return 'number';
        case 'date': return 'datetime-local';
        default: return 'text';
      }
    });

    Handlebars.registerHelper('isTextArea', (type: string, validation?: string) => {
      // Use textarea for string types with 'multiline' hint or large maxLength
      if (type !== 'string') return false;
        if (validation) {
          if (validation.includes('multiline')) return true;
          const maxLengthMatch = validation.match(/maxLength:(\d+)/);
          const maxLen = maxLengthMatch?.[1] ? parseInt(maxLengthMatch[1], 10) : undefined;
          if (maxLen !== undefined && maxLen > 255) return true;
        }
      return false;
    });

    Handlebars.registerHelper('isSelect', (type: string, validation?: string) => {
      return validation?.includes('enum:');
    });

    Handlebars.registerHelper('isBoolean', (type: string) => {
      return type === 'boolean';
    });

    Handlebars.registerHelper('isNumber', (type: string) => {
      return type === 'number';
    });

    Handlebars.registerHelper('getSelectOptions', (validation?: string) => {
      if (!validation?.includes('enum:')) return [];
      const enumMatch = validation.match(/enum:([^,]+)/);
      const group = enumMatch?.[1] ?? '';
      return group ? group.split('|').map(s => s.trim()) : [];
    });

    Handlebars.registerHelper('getMockValue', (type: string, validation?: string, key?: string) => {
      switch (type) {
        case 'string':
          if (validation?.includes('enum:')) {
            const enumStr = validation.match(/enum:([^,]+)/)?.[1];
            const options = enumStr ? enumStr.split('|').map(s => s.trim()) : [];
            return `"${options[0] || 'active'}"`;
          }
          return `"Sample ${key || 'text'}"`;
        case 'number':
          return key?.toLowerCase().includes('price') ? '99.99' : '42';
        case 'boolean':
          return 'true';
        case 'date':
          return '"2024-01-01T00:00:00.000Z"';
        case 'array':
          return '[]';
        case 'object':
          return '{}';
        default:
          return 'null';
      }
    });

    Handlebars.registerHelper('getTestValue', (type: string, key?: string) => {
      switch (type) {
        case 'string':
          return `Test ${key || 'Value'}`;
        case 'number':
          return '100';
        case 'boolean':
          return 'true';
        case 'date':
          return '2024-01-01';
        default:
          return 'test';
      }
    });

    Handlebars.registerHelper('getFieldDisplay', (key: string, entityName: string) => {
      return `{${entityName}.${key}}`;
    });

    Handlebars.registerHelper('getCardFieldDisplay', (key: string, entityName: string) => {
      const entity = `{${entityName}.${key}}`;
      
      // Add formatting for specific types
      if (key.toLowerCase().includes('price') || key.toLowerCase().includes('total')) {
        return `$${entity}`;
      }
      if (key.toLowerCase().includes('date') || key.toLowerCase().includes('at')) {
        return `{new Date(${entityName}.${key}).toLocaleDateString()}`;
      }
      
      return entity;
    });

    Handlebars.registerHelper('first', (arr: any[]) => {
      return arr?.[0];
    });
  }
}
