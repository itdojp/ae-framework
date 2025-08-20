#!/usr/bin/env node

/**
 * IR Schema Strictness Validator
 * Demonstrates enhanced validation for AE-IR schemas
 */

import fs from 'fs';
import path from 'path';

class IRSchemaValidator {
  constructor() {
    this.rules = [
      {
        id: 'IR_001',
        name: 'Version Format',
        description: 'Version must follow semantic versioning',
        validate: (ir) => {
          const versionRegex = /^\d+\.\d+\.\d+(-[a-zA-Z0-9\-.]+)?(\+[a-zA-Z0-9\-.]+)?$/;
          return versionRegex.test(ir.version);
        },
        severity: 'error'
      },
      {
        id: 'IR_002',
        name: 'Metadata Completeness',
        description: 'Metadata must have name, created, and updated dates',
        validate: (ir) => {
          const meta = ir.metadata;
          return meta && meta.name && meta.created && meta.updated;
        },
        severity: 'error'
      },
      {
        id: 'IR_003',
        name: 'Entity Field Types',
        description: 'Entity fields must have valid types',
        validate: (ir) => {
          const validTypes = ['string', 'number', 'boolean', 'date', 'uuid', 'email', 'url', 'json', 'array', 'object'];
          for (const entity of ir.domain || []) {
            for (const field of entity.fields || []) {
              if (!validTypes.includes(field.type)) {
                return false;
              }
            }
          }
          return true;
        },
        severity: 'error'
      },
      {
        id: 'IR_004',
        name: 'Unique Entity Names',
        description: 'All entity names must be unique',
        validate: (ir) => {
          const names = new Set();
          for (const entity of ir.domain || []) {
            if (names.has(entity.name)) {
              return false;
            }
            names.add(entity.name);
          }
          return true;
        },
        severity: 'error'
      },
      {
        id: 'IR_005',
        name: 'Unique Field Names',
        description: 'Field names within each entity must be unique',
        validate: (ir) => {
          for (const entity of ir.domain || []) {
            const fieldNames = new Set();
            for (const field of entity.fields || []) {
              if (fieldNames.has(field.name)) {
                return false;
              }
              fieldNames.add(field.name);
            }
          }
          return true;
        },
        severity: 'error'
      },
      {
        id: 'IR_006',
        name: 'API Path Format',
        description: 'API paths must start with /',
        validate: (ir) => {
          for (const endpoint of ir.api || []) {
            if (!endpoint.path.startsWith('/')) {
              return false;
            }
          }
          return true;
        },
        severity: 'error'
      },
      {
        id: 'IR_007',
        name: 'Use Case Steps Sequential',
        description: 'Use case steps must be numbered sequentially',
        validate: (ir) => {
          for (const usecase of ir.usecases || []) {
            const steps = usecase.steps || [];
            for (let i = 0; i < steps.length; i++) {
              if (steps[i].step !== i + 1) {
                return false;
              }
            }
          }
          return true;
        },
        severity: 'warning'
      },
      {
        id: 'IR_008',
        name: 'Identifier Format',
        description: 'Names must be valid identifiers',
        validate: (ir) => {
          const identifierRegex = /^[a-zA-Z_][a-zA-Z0-9_]*$/;
          
          // Check entity names
          for (const entity of ir.domain || []) {
            if (!identifierRegex.test(entity.name)) {
              return false;
            }
            
            // Check field names
            for (const field of entity.fields || []) {
              if (!identifierRegex.test(field.name)) {
                return false;
              }
            }
          }
          return true;
        },
        severity: 'error'
      },
      {
        id: 'IR_009',
        name: 'Cross References',
        description: 'State machines must reference existing entities',
        validate: (ir) => {
          const entityNames = new Set((ir.domain || []).map(e => e.name));
          for (const sm of ir.statemachines || []) {
            if (!entityNames.has(sm.entity)) {
              return false;
            }
          }
          return true;
        },
        severity: 'error'
      },
      {
        id: 'IR_010',
        name: 'Required Fields Presence',
        description: 'Entities should have at least one required field',
        validate: (ir) => {
          for (const entity of ir.domain || []) {
            const hasRequired = (entity.fields || []).some(f => f.required);
            if (!hasRequired) {
              return false;
            }
          }
          return true;
        },
        severity: 'warning'
      }
    ];
  }

  validateFile(filePath) {
    try {
      const content = fs.readFileSync(filePath, 'utf-8');
      const ir = JSON.parse(content);
      return this.validate(ir);
    } catch (error) {
      return {
        valid: false,
        errors: [{
          id: 'PARSE_ERROR',
          severity: 'error',
          message: `Failed to parse IR file: ${error.message}`
        }],
        warnings: [],
        info: []
      };
    }
  }

  validate(ir) {
    const errors = [];
    const warnings = [];
    const info = [];

    for (const rule of this.rules) {
      try {
        const result = rule.validate(ir);
        
        if (!result) {
          const issue = {
            id: rule.id,
            name: rule.name,
            description: rule.description,
            severity: rule.severity,
            message: `${rule.name}: ${rule.description}`
          };

          if (rule.severity === 'error') {
            errors.push(issue);
          } else if (rule.severity === 'warning') {
            warnings.push(issue);
          } else {
            info.push(issue);
          }
        }
      } catch (error) {
        errors.push({
          id: 'VALIDATION_ERROR',
          severity: 'error',
          message: `Rule ${rule.id} failed: ${error.message}`
        });
      }
    }

    const passed = this.rules.length - errors.length - warnings.length - info.length;
    
    return {
      valid: errors.length === 0,
      errors,
      warnings,
      info,
      summary: {
        totalRules: this.rules.length,
        passed: passed,
        errors: errors.length,
        warnings: warnings.length,
        info: info.length
      }
    };
  }

  generateReport(result) {
    let report = '# IR Schema Validation Report\n\n';
    
    report += `**Status:** ${result.valid ? '✅ VALID' : '❌ INVALID'}\n`;
    report += `**Rules Checked:** ${result.summary.totalRules}\n`;
    report += `**Passed:** ${result.summary.passed}\n`;
    report += `**Errors:** ${result.summary.errors}\n`;
    report += `**Warnings:** ${result.summary.warnings}\n\n`;

    if (result.errors.length > 0) {
      report += '## 🚨 Errors\n\n';
      for (const error of result.errors) {
        report += `- **${error.id}**: ${error.message}\n`;
      }
      report += '\n';
    }

    if (result.warnings.length > 0) {
      report += '## ⚠️ Warnings\n\n';
      for (const warning of result.warnings) {
        report += `- **${warning.id}**: ${warning.message}\n`;
      }
      report += '\n';
    }

    if (result.valid) {
      report += '## ✅ All validations passed!\n\n';
      report += 'The IR schema meets all strictness requirements.\n';
    } else {
      report += '## 📋 Recommendations\n\n';
      report += '1. Fix all error-level issues before proceeding\n';
      report += '2. Consider addressing warnings for better quality\n';
      report += '3. Ensure all cross-references are valid\n';
    }

    return report;
  }

  async validateProject(projectDir = '.') {
    const results = [];
    const irFiles = this.findIRFiles(projectDir);
    
    console.log(`🔍 Found ${irFiles.length} IR files to validate...`);
    
    for (const file of irFiles) {
      console.log(`📄 Validating: ${file}`);
      const result = this.validateFile(file);
      result.file = file;
      results.push(result);
    }

    // Generate summary
    const overallValid = results.every(r => r.valid);
    const totalErrors = results.reduce((sum, r) => sum + r.errors.length, 0);
    const totalWarnings = results.reduce((sum, r) => sum + r.warnings.length, 0);

    console.log(`\n📊 Validation Summary:`);
    console.log(`   Files validated: ${results.length}`);
    console.log(`   Overall status: ${overallValid ? '✅ VALID' : '❌ INVALID'}`);
    console.log(`   Total errors: ${totalErrors}`);
    console.log(`   Total warnings: ${totalWarnings}`);

    // Save detailed report
    if (results.length > 0) {
      const reportPath = path.join(projectDir, 'ir-validation-report.md');
      let fullReport = '# Project IR Schema Validation Report\n\n';
      
      fullReport += `**Generated:** ${new Date().toISOString()}\n`;
      fullReport += `**Files Validated:** ${results.length}\n`;
      fullReport += `**Overall Status:** ${overallValid ? '✅ VALID' : '❌ INVALID'}\n\n`;

      for (const result of results) {
        fullReport += `## File: ${result.file}\n\n`;
        fullReport += this.generateReport(result);
        fullReport += '\n---\n\n';
      }

      fs.writeFileSync(reportPath, fullReport);
      console.log(`\n📄 Detailed report saved: ${reportPath}`);
    }

    return { results, overallValid, totalErrors, totalWarnings };
  }

  findIRFiles(dir) {
    const files = [];
    
    try {
      const entries = fs.readdirSync(dir, { withFileTypes: true });
      
      for (const entry of entries) {
        const fullPath = path.join(dir, entry.name);
        
        if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
          files.push(...this.findIRFiles(fullPath));
        } else if (entry.isFile() && (entry.name.endsWith('-ir.json') || entry.name.endsWith('.aeir.json'))) {
          files.push(fullPath);
        }
      }
    } catch (error) {
      console.warn(`Warning: Could not scan directory ${dir}: ${error.message}`);
    }
    
    return files;
  }

  createSampleIR() {
    return {
      version: '1.0.0',
      metadata: {
        name: 'sample_project',
        description: 'A sample project for demonstrating IR validation',
        created: '2023-01-01T00:00:00.000Z',
        updated: '2023-01-01T12:00:00.000Z'
      },
      glossary: [
        { term: 'User', definition: 'A person who uses the system' }
      ],
      domain: [
        {
          name: 'User',
          description: 'User entity',
          fields: [
            { name: 'id', type: 'uuid', required: true },
            { name: 'name', type: 'string', required: true },
            { name: 'email', type: 'email', required: false }
          ]
        }
      ],
      invariants: [],
      usecases: [
        {
          name: 'Create User',
          description: 'Create a new user',
          actor: 'Admin',
          steps: [
            { step: 1, description: 'Validate input', type: 'validation' },
            { step: 2, description: 'Create user', type: 'action' }
          ]
        }
      ],
      api: [
        { method: 'POST', path: '/users', summary: 'Create user' }
      ]
    };
  }
}

// CLI interface
if (process.argv[1] === new URL(import.meta.url).pathname) {
  const args = process.argv.slice(2);
  const validator = new IRSchemaValidator();

  if (args.includes('--help') || args.includes('-h')) {
    console.log(`
IR Schema Strictness Validator

Usage:
  node ir-schema-validator.js [options] [file]

Options:
  --help, -h        Show this help
  --project [dir]   Validate all IR files in project directory
  --sample          Create a sample valid IR file
  --rules           List all validation rules

Examples:
  node ir-schema-validator.js my-spec.aeir.json
  node ir-schema-validator.js --project .
  node ir-schema-validator.js --sample > sample.aeir.json
`);
    process.exit(0);
  }

  if (args.includes('--rules')) {
    console.log('📋 IR Schema Validation Rules:\n');
    validator.rules.forEach(rule => {
      console.log(`${rule.id}: ${rule.name} (${rule.severity})`);
      console.log(`   ${rule.description}\n`);
    });
    process.exit(0);
  }

  if (args.includes('--sample')) {
    console.log(JSON.stringify(validator.createSampleIR(), null, 2));
    process.exit(0);
  }

  if (args.includes('--project')) {
    const projectDir = args[args.indexOf('--project') + 1] || '.';
    validator.validateProject(projectDir).then(result => {
      process.exit(result.overallValid ? 0 : 1);
    });
  } else if (args.length > 0) {
    const file = args[0];
    console.log(`🔍 Validating IR file: ${file}`);
    const result = validator.validateFile(file);
    
    console.log(validator.generateReport(result));
    process.exit(result.valid ? 0 : 1);
  } else {
    console.log('Please provide a file to validate or use --project flag. Use --help for usage info.');
    process.exit(1);
  }
}

export { IRSchemaValidator };