/**
 * Document Command for ae-framework
 * Generates comprehensive documentation for code
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import * as ts from 'typescript';
import type { CommandResult, CommandContext } from '../slash-command-manager.js';
import { EvidenceValidator } from '../../utils/evidence-validator.js';

export interface DocumentationResult {
  file: string;
  documentation: Documentation;
  format: 'markdown' | 'jsdoc' | 'api-json';
  written: boolean;
}

export interface Documentation {
  summary: string;
  description?: string;
  exports: ExportedItem[];
  dependencies: string[];
  examples?: Example[];
  metadata: Metadata;
}

export interface ExportedItem {
  name: string;
  type: 'function' | 'class' | 'interface' | 'type' | 'constant' | 'enum';
  signature?: string;
  description?: string;
  parameters?: Parameter[];
  returns?: ReturnValue;
  properties?: Property[];
  methods?: Method[];
}

export interface Parameter {
  name: string;
  type: string;
  description?: string;
  optional?: boolean;
  defaultValue?: string;
}

export interface ReturnValue {
  type: string;
  description?: string;
}

export interface Property {
  name: string;
  type: string;
  description?: string;
  access?: 'public' | 'private' | 'protected';
}

export interface Method {
  name: string;
  signature: string;
  description?: string;
  access?: 'public' | 'private' | 'protected';
  parameters?: Parameter[];
  returns?: ReturnValue;
}

export interface Example {
  title: string;
  code: string;
  description?: string;
}

export interface Metadata {
  author?: string;
  version?: string;
  license?: string;
  tags?: string[];
  complexity?: number;
  linesOfCode: number;
}

export class DocumentCommand {
  private validator: EvidenceValidator;

  constructor() {
    this.validator = new EvidenceValidator();
  }

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a file or directory to document'
      };
    }

    const target = args[0];
    const options = this.parseOptions(args.slice(1));

    try {
      const results = await this.document(target, options);
      const summary = this.generateSummary(results);

      return {
        success: true,
        message: summary,
        data: results
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Documentation generation failed: ${error.message}`
      };
    }
  }

  private parseOptions(args: string[]): any {
    const options: any = {
      format: 'markdown',
      output: null,
      includePrivate: false,
      includeExamples: true,
      write: false
    };

    for (let i = 0; i < args.length; i++) {
      switch (args[i]) {
        case '--format':
          options.format = args[++i] || 'markdown';
          break;
        case '--output':
          options.output = args[++i];
          break;
        case '--include-private':
          options.includePrivate = true;
          break;
        case '--no-examples':
          options.includeExamples = false;
          break;
        case '--write':
          options.write = true;
          break;
      }
    }

    return options;
  }

  private async document(target: string, options: any): Promise<DocumentationResult[]> {
    const results: DocumentationResult[] = [];
    const stats = await fs.stat(target);

    if (stats.isDirectory()) {
      const files = await this.findSourceFiles(target);
      for (const file of files) {
        const result = await this.documentFile(file, options);
        results.push(result);
      }
    } else {
      const result = await this.documentFile(target, options);
      results.push(result);
    }

    return results;
  }

  private async findSourceFiles(dir: string): Promise<string[]> {
    const files: string[] = [];
    const entries = await fs.readdir(dir, { withFileTypes: true });

    for (const entry of entries) {
      const fullPath = path.join(dir, entry.name);
      
      if (entry.isDirectory() && !entry.name.startsWith('.') && 
          entry.name !== 'node_modules' && entry.name !== 'dist') {
        const subFiles = await this.findSourceFiles(fullPath);
        files.push(...subFiles);
      } else if (entry.isFile() && 
                (entry.name.endsWith('.ts') || entry.name.endsWith('.js')) &&
                !entry.name.includes('.test.') && !entry.name.includes('.spec.')) {
        files.push(fullPath);
      }
    }

    return files;
  }

  private async documentFile(file: string, options: any): Promise<DocumentationResult> {
    const content = await fs.readFile(file, 'utf-8');
    
    // Parse the file
    const exports = this.extractExports(content, file);
    const dependencies = this.extractDependencies(content);
    const examples = options.includeExamples ? this.extractExamples(content) : [];
    const metadata = await this.extractMetadata(content, file);

    const documentation: Documentation = {
      summary: this.generateSummary(exports),
      description: this.extractFileDescription(content),
      exports,
      dependencies,
      examples,
      metadata
    };

    // Format documentation
    let formatted: string;
    switch (options.format) {
      case 'jsdoc':
        formatted = this.formatAsJSDoc(documentation, file);
        break;
      case 'api-json':
        formatted = JSON.stringify(documentation, null, 2);
        break;
      default:
        formatted = this.formatAsMarkdown(documentation, file);
    }

    // Write documentation if requested
    let written = false;
    if (options.write) {
      const outputPath = options.output || this.getDefaultOutputPath(file, options.format);
      await fs.writeFile(outputPath, formatted, 'utf-8');
      written = true;
    }

    return {
      file,
      documentation,
      format: options.format,
      written
    };
  }

  private extractExports(content: string, file: string): ExportedItem[] {
    const exports: ExportedItem[] = [];

    if (file.endsWith('.ts')) {
      const sourceFile = ts.createSourceFile(
        file,
        content,
        ts.ScriptTarget.Latest,
        true
      );

      const visit = (node: ts.Node) => {
        if (ts.isExportAssignment(node) || ts.isExportDeclaration(node)) {
          // Handle export statements
        } else if (ts.isFunctionDeclaration(node) && node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) {
          exports.push(this.extractFunction(node));
        } else if (ts.isClassDeclaration(node) && node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) {
          exports.push(this.extractClass(node));
        } else if (ts.isInterfaceDeclaration(node) && node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) {
          exports.push(this.extractInterface(node));
        } else if (ts.isTypeAliasDeclaration(node) && node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) {
          exports.push(this.extractTypeAlias(node));
        } else if (ts.isEnumDeclaration(node) && node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) {
          exports.push(this.extractEnum(node));
        } else if (ts.isVariableStatement(node) && node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) {
          node.declarationList.declarations.forEach(decl => {
            if (ts.isIdentifier(decl.name)) {
              exports.push({
                name: decl.name.text,
                type: 'constant',
                signature: decl.getText()
              });
            }
          });
        }

        ts.forEachChild(node, visit);
      };

      visit(sourceFile);
    } else {
      // For JavaScript files, use regex patterns
      const functionPattern = /export\s+(async\s+)?function\s+(\w+)/g;
      const classPattern = /export\s+class\s+(\w+)/g;
      const constPattern = /export\s+const\s+(\w+)/g;

      let match;
      while ((match = functionPattern.exec(content)) !== null) {
        exports.push({
          name: match[2],
          type: 'function',
          signature: match[0]
        });
      }

      while ((match = classPattern.exec(content)) !== null) {
        exports.push({
          name: match[1],
          type: 'class',
          signature: match[0]
        });
      }

      while ((match = constPattern.exec(content)) !== null) {
        exports.push({
          name: match[1],
          type: 'constant',
          signature: match[0]
        });
      }
    }

    return exports;
  }

  private extractFunction(node: ts.FunctionDeclaration): ExportedItem {
    const name = node.name?.text || 'anonymous';
    const parameters = node.parameters.map(param => ({
      name: param.name.getText(),
      type: param.type?.getText() || 'any',
      optional: !!param.questionToken,
      defaultValue: param.initializer?.getText()
    }));

    const returnType = node.type?.getText() || 'void';

    return {
      name,
      type: 'function',
      signature: node.getText().split('{')[0].trim(),
      parameters,
      returns: { type: returnType }
    };
  }

  private extractClass(node: ts.ClassDeclaration): ExportedItem {
    const name = node.name?.text || 'anonymous';
    const properties: Property[] = [];
    const methods: Method[] = [];

    node.members.forEach(member => {
      if (ts.isPropertyDeclaration(member)) {
        const propName = member.name?.getText() || '';
        properties.push({
          name: propName,
          type: member.type?.getText() || 'any',
          access: this.getAccessModifier(member)
        });
      } else if (ts.isMethodDeclaration(member)) {
        const methodName = member.name?.getText() || '';
        const parameters = member.parameters.map(param => ({
          name: param.name.getText(),
          type: param.type?.getText() || 'any',
          optional: !!param.questionToken
        }));
        
        methods.push({
          name: methodName,
          signature: member.getText().split('{')[0].trim(),
          access: this.getAccessModifier(member),
          parameters,
          returns: { type: member.type?.getText() || 'void' }
        });
      }
    });

    return {
      name,
      type: 'class',
      signature: `class ${name}`,
      properties,
      methods
    };
  }

  private extractInterface(node: ts.InterfaceDeclaration): ExportedItem {
    const name = node.name.text;
    const properties: Property[] = [];

    node.members.forEach(member => {
      if (ts.isPropertySignature(member)) {
        const propName = member.name?.getText() || '';
        properties.push({
          name: propName,
          type: member.type?.getText() || 'any'
        });
      }
    });

    return {
      name,
      type: 'interface',
      signature: `interface ${name}`,
      properties
    };
  }

  private extractTypeAlias(node: ts.TypeAliasDeclaration): ExportedItem {
    return {
      name: node.name.text,
      type: 'type',
      signature: node.getText()
    };
  }

  private extractEnum(node: ts.EnumDeclaration): ExportedItem {
    const name = node.name.text;
    const properties = node.members.map(member => ({
      name: member.name?.getText() || '',
      type: 'enum member',
      description: member.initializer?.getText()
    }));

    return {
      name,
      type: 'enum',
      signature: `enum ${name}`,
      properties
    };
  }

  private getAccessModifier(member: ts.ClassElement): 'public' | 'private' | 'protected' {
    if (member.modifiers) {
      if (member.modifiers.some(m => m.kind === ts.SyntaxKind.PrivateKeyword)) return 'private';
      if (member.modifiers.some(m => m.kind === ts.SyntaxKind.ProtectedKeyword)) return 'protected';
    }
    return 'public';
  }

  private extractDependencies(content: string): string[] {
    const dependencies: Set<string> = new Set();
    
    // Extract import statements
    const importPattern = /import\s+.*?\s+from\s+['"]([^'"]+)['"]/g;
    const requirePattern = /require\s*\(['"]([^'"]+)['"]\)/g;
    
    let match;
    while ((match = importPattern.exec(content)) !== null) {
      dependencies.add(match[1]);
    }
    while ((match = requirePattern.exec(content)) !== null) {
      dependencies.add(match[1]);
    }

    return Array.from(dependencies);
  }

  private extractExamples(content: string): Example[] {
    const examples: Example[] = [];
    
    // Extract examples from comments
    const examplePattern = /\/\*\*[\s\S]*?@example([\s\S]*?)\*\//g;
    let match;
    
    while ((match = examplePattern.exec(content)) !== null) {
      const exampleContent = match[1].trim();
      const lines = exampleContent.split('\n').map(l => l.replace(/^\s*\*\s?/, ''));
      
      examples.push({
        title: 'Example',
        code: lines.join('\n')
      });
    }

    // Also look for markdown code blocks in comments
    const codeBlockPattern = /\/\/\s*```([\s\S]*?)```/g;
    while ((match = codeBlockPattern.exec(content)) !== null) {
      examples.push({
        title: 'Code Example',
        code: match[1].trim()
      });
    }

    return examples;
  }

  private extractFileDescription(content: string): string | undefined {
    // Look for file-level JSDoc comment
    const fileCommentPattern = /^\/\*\*([\s\S]*?)\*\//;
    const match = content.match(fileCommentPattern);
    
    if (match) {
      const comment = match[1]
        .split('\n')
        .map(line => line.replace(/^\s*\*\s?/, ''))
        .join('\n')
        .trim();
      
      // Return first paragraph as description
      return comment.split('\n\n')[0];
    }
    
    return undefined;
  }

  private async extractMetadata(content: string, file: string): Promise<Metadata> {
    const lines = content.split('\n');
    const metadata: Metadata = {
      linesOfCode: lines.length
    };

    // Try to extract from package.json if available
    try {
      const packageJson = await fs.readFile(path.join(process.cwd(), 'package.json'), 'utf-8');
      const pkg = JSON.parse(packageJson);
      metadata.author = pkg.author;
      metadata.version = pkg.version;
      metadata.license = pkg.license;
    } catch {
      // Package.json not available
    }

    // Extract tags from comments
    const tagPattern = /@tag\s+(\w+)/g;
    const tags: string[] = [];
    let match;
    while ((match = tagPattern.exec(content)) !== null) {
      tags.push(match[1]);
    }
    if (tags.length > 0) {
      metadata.tags = tags;
    }

    // Calculate complexity (simplified)
    metadata.complexity = this.calculateComplexity(content);

    return metadata;
  }

  private calculateComplexity(content: string): number {
    let complexity = 1;
    
    // Count decision points
    const patterns = [
      /if\s*\(/g,
      /for\s*\(/g,
      /while\s*\(/g,
      /case\s+/g,
      /catch\s*\(/g
    ];

    for (const pattern of patterns) {
      const matches = content.match(pattern);
      if (matches) {
        complexity += matches.length;
      }
    }

    return complexity;
  }

  private generateSummary(exports: ExportedItem[]): string {
    const counts: Record<string, number> = {};
    
    for (const item of exports) {
      counts[item.type] = (counts[item.type] || 0) + 1;
    }

    const parts: string[] = [];
    for (const [type, count] of Object.entries(counts)) {
      parts.push(`${count} ${type}${count > 1 ? 's' : ''}`);
    }

    return parts.length > 0 ? `Exports ${parts.join(', ')}` : 'No exports';
  }

  private formatAsMarkdown(doc: Documentation, file: string): string {
    let md = `# ${path.basename(file)}\n\n`;
    
    if (doc.description) {
      md += `${doc.description}\n\n`;
    }

    md += `## Summary\n\n${doc.summary}\n\n`;

    if (doc.dependencies.length > 0) {
      md += `## Dependencies\n\n`;
      for (const dep of doc.dependencies) {
        md += `- ${dep}\n`;
      }
      md += '\n';
    }

    if (doc.exports.length > 0) {
      md += `## Exports\n\n`;
      
      for (const exp of doc.exports) {
        md += `### ${exp.name}\n\n`;
        md += `**Type:** ${exp.type}\n\n`;
        
        if (exp.signature) {
          md += '```typescript\n';
          md += exp.signature;
          md += '\n```\n\n';
        }

        if (exp.description) {
          md += `${exp.description}\n\n`;
        }

        if (exp.parameters && exp.parameters.length > 0) {
          md += '**Parameters:**\n\n';
          for (const param of exp.parameters) {
            md += `- \`${param.name}\` (${param.type})`;
            if (param.optional) md += ' _optional_';
            if (param.defaultValue) md += ` = ${param.defaultValue}`;
            if (param.description) md += ` - ${param.description}`;
            md += '\n';
          }
          md += '\n';
        }

        if (exp.returns) {
          md += `**Returns:** ${exp.returns.type}`;
          if (exp.returns.description) md += ` - ${exp.returns.description}`;
          md += '\n\n';
        }

        if (exp.properties && exp.properties.length > 0) {
          md += '**Properties:**\n\n';
          for (const prop of exp.properties) {
            md += `- \`${prop.name}\` (${prop.type})`;
            if (prop.access && prop.access !== 'public') md += ` _${prop.access}_`;
            if (prop.description) md += ` - ${prop.description}`;
            md += '\n';
          }
          md += '\n';
        }

        if (exp.methods && exp.methods.length > 0) {
          md += '**Methods:**\n\n';
          for (const method of exp.methods) {
            md += `- \`${method.name}\``;
            if (method.access && method.access !== 'public') md += ` _${method.access}_`;
            if (method.description) md += ` - ${method.description}`;
            md += '\n';
          }
          md += '\n';
        }
      }
    }

    if (doc.examples && doc.examples.length > 0) {
      md += `## Examples\n\n`;
      for (const example of doc.examples) {
        md += `### ${example.title}\n\n`;
        if (example.description) {
          md += `${example.description}\n\n`;
        }
        md += '```typescript\n';
        md += example.code;
        md += '\n```\n\n';
      }
    }

    if (doc.metadata) {
      md += `## Metadata\n\n`;
      md += `- **Lines of Code:** ${doc.metadata.linesOfCode}\n`;
      md += `- **Complexity:** ${doc.metadata.complexity}\n`;
      if (doc.metadata.author) md += `- **Author:** ${doc.metadata.author}\n`;
      if (doc.metadata.version) md += `- **Version:** ${doc.metadata.version}\n`;
      if (doc.metadata.license) md += `- **License:** ${doc.metadata.license}\n`;
      if (doc.metadata.tags) md += `- **Tags:** ${doc.metadata.tags.join(', ')}\n`;
    }

    return md;
  }

  private formatAsJSDoc(doc: Documentation, file: string): string {
    let jsdoc = '/**\n';
    jsdoc += ` * @file ${path.basename(file)}\n`;
    
    if (doc.description) {
      jsdoc += ` * @description ${doc.description}\n`;
    }
    
    if (doc.metadata) {
      if (doc.metadata.author) jsdoc += ` * @author ${doc.metadata.author}\n`;
      if (doc.metadata.version) jsdoc += ` * @version ${doc.metadata.version}\n`;
      if (doc.metadata.license) jsdoc += ` * @license ${doc.metadata.license}\n`;
    }
    
    jsdoc += ' */\n\n';

    // Add JSDoc for each export
    for (const exp of doc.exports) {
      jsdoc += '/**\n';
      
      if (exp.description) {
        jsdoc += ` * ${exp.description}\n`;
      }
      
      if (exp.parameters) {
        for (const param of exp.parameters) {
          jsdoc += ` * @param {${param.type}} ${param.name}`;
          if (param.description) jsdoc += ` - ${param.description}`;
          jsdoc += '\n';
        }
      }
      
      if (exp.returns) {
        jsdoc += ` * @returns {${exp.returns.type}}`;
        if (exp.returns.description) jsdoc += ` ${exp.returns.description}`;
        jsdoc += '\n';
      }
      
      jsdoc += ' */\n';
      
      if (exp.signature) {
        jsdoc += exp.signature + '\n\n';
      }
    }

    return jsdoc;
  }

  private getDefaultOutputPath(file: string, format: string): string {
    const dir = path.dirname(file);
    const base = path.basename(file, path.extname(file));
    
    switch (format) {
      case 'markdown':
        return path.join(dir, `${base}.md`);
      case 'api-json':
        return path.join(dir, `${base}.api.json`);
      default:
        return path.join(dir, `${base}.docs.js`);
    }
  }

  private generateSummary(results: DocumentationResult[]): string {
    let summary = `Documented ${results.length} file(s)\n\n`;
    
    let totalExports = 0;
    let writtenCount = 0;
    const types: Record<string, number> = {};

    for (const result of results) {
      totalExports += result.documentation.exports.length;
      if (result.written) writtenCount++;

      for (const exp of result.documentation.exports) {
        types[exp.type] = (types[exp.type] || 0) + 1;
      }
    }

    summary += `Total exports documented: ${totalExports}\n`;
    
    if (writtenCount > 0) {
      summary += `Documentation files written: ${writtenCount}\n`;
    }

    if (Object.keys(types).length > 0) {
      summary += '\nExports by type:\n';
      for (const [type, count] of Object.entries(types)) {
        summary += `  ${type}: ${count}\n`;
      }
    }

    return summary;
  }
}