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
  optional?: boolean;
  access?: 'public' | 'private' | 'protected';
}

export interface Method {
  name: string;
  signature: string;
  description?: string;
  parameters?: Parameter[];
  returns?: ReturnValue;
  access?: 'public' | 'private' | 'protected';
}

export interface Example {
  title: string;
  code: string;
  description?: string;
}

export interface Metadata {
  author?: string;
  version?: string;
  lastModified: string;
  fileSize: number;
  linesOfCode: number;
  complexity: number;
}

export class DocumentCommand {
  name = '/ae:document';
  description = 'Generate comprehensive documentation';
  category = 'utility' as const;
  usage = '/ae:document <file|directory> [--format=markdown|jsdoc|api-json] [--output=path]';
  aliases = ['/document', '/a:document'];

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
      const results = await this.generateDocumentation(target, options);
      const summary = this.generateSummary(results);

      // Optionally validate documentation completeness
      if (options.validate) {
        for (const result of results) {
          const validation = await this.validator.validateClaim(
            `Documentation completeness for ${result.file}`,
            JSON.stringify(result.documentation),
            { minConfidence: 0.6 }
          );
          
          if (validation.confidence < 0.6) {
            return {
              success: false,
              message: `Documentation validation failed for ${result.file}: ${validation.reasoning}`
            };
          }
        }
      }

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
      writeFiles: false,
      includePrivate: false,
      validate: false
    };

    for (let i = 0; i < args.length; i++) {
      const arg = args[i];
      if (arg.startsWith('--format=')) {
        options.format = arg.split('=')[1];
      } else if (arg.startsWith('--output=')) {
        options.output = arg.split('=')[1];
        options.writeFiles = true;
      } else if (arg === '--include-private') {
        options.includePrivate = true;
      } else if (arg === '--validate') {
        options.validate = true;
      }
    }

    return options;
  }

  private async generateDocumentation(target: string, options: any): Promise<DocumentationResult[]> {
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
      
      if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
        const subFiles = await this.findSourceFiles(fullPath);
        files.push(...subFiles);
      } else if (entry.isFile() && (entry.name.endsWith('.ts') || entry.name.endsWith('.js'))) {
        files.push(fullPath);
      }
    }

    return files;
  }

  private async documentFile(file: string, options: any): Promise<DocumentationResult> {
    const content = await fs.readFile(file, 'utf-8');
    const stats = await fs.stat(file);
    
    const documentation = await this.parseAndDocument(content, file, options);
    let written = false;

    if (options.writeFiles && options.output) {
      const outputPath = this.getOutputPath(file, options.output, options.format);
      const formatted = this.formatDocumentation(documentation, options.format);
      await fs.writeFile(outputPath, formatted);
      written = true;
    }

    return {
      file,
      documentation,
      format: options.format,
      written
    };
  }

  private async parseAndDocument(content: string, filePath: string, options: any): Promise<Documentation> {
    const sourceFile = ts.createSourceFile(
      filePath,
      content,
      ts.ScriptTarget.Latest,
      true
    );

    const exports = this.extractExports(sourceFile, options.includePrivate);
    const dependencies = this.extractDependencies(content);
    const examples = this.extractExamples(content);
    const metadata = await this.generateMetadata(content, filePath);

    return {
      summary: this.generateSummary(exports),
      description: this.extractDescription(content),
      exports,
      dependencies,
      examples,
      metadata
    };
  }

  private extractExports(sourceFile: ts.SourceFile, includePrivate: boolean = false): ExportedItem[] {
    const exports: ExportedItem[] = [];

    const visit = (node: ts.Node) => {
      // Functions
      if (ts.isFunctionDeclaration(node) && node.name) {
        const isPrivate = this.hasPrivateModifier(node);
        if (!isPrivate || includePrivate) {
          exports.push(this.createFunctionItem(node));
        }
      }
      
      // Classes
      if (ts.isClassDeclaration(node) && node.name) {
        const isPrivate = this.hasPrivateModifier(node);
        if (!isPrivate || includePrivate) {
          exports.push(this.createClassItem(node, includePrivate));
        }
      }
      
      // Interfaces
      if (ts.isInterfaceDeclaration(node)) {
        exports.push(this.createInterfaceItem(node));
      }
      
      // Type aliases
      if (ts.isTypeAliasDeclaration(node)) {
        exports.push(this.createTypeItem(node));
      }
      
      // Constants and variables
      if (ts.isVariableStatement(node)) {
        const isPrivate = this.hasPrivateModifier(node);
        if (!isPrivate || includePrivate) {
          for (const declaration of node.declarationList.declarations) {
            if (ts.isIdentifier(declaration.name)) {
              exports.push(this.createConstantItem(declaration));
            }
          }
        }
      }
      
      // Enums
      if (ts.isEnumDeclaration(node)) {
        const isPrivate = this.hasPrivateModifier(node);
        if (!isPrivate || includePrivate) {
          exports.push(this.createEnumItem(node));
        }
      }

      ts.forEachChild(node, visit);
    };

    visit(sourceFile);
    return exports;
  }

  private hasPrivateModifier(node: ts.Node): boolean {
    return node.modifiers?.some(mod => mod.kind === ts.SyntaxKind.PrivateKeyword) ?? false;
  }

  private createFunctionItem(node: ts.FunctionDeclaration): ExportedItem {
    return {
      name: node.name!.getText(),
      type: 'function',
      signature: this.getFunctionSignature(node),
      description: this.extractJSDocComment(node),
      parameters: this.extractParameters(node),
      returns: this.extractReturnType(node)
    };
  }

  private createClassItem(node: ts.ClassDeclaration, includePrivate: boolean): ExportedItem {
    const methods: Method[] = [];
    const properties: Property[] = [];

    for (const member of node.members) {
      const isPrivate = this.hasPrivateModifier(member);
      
      if (ts.isMethodDeclaration(member) && member.name && (!isPrivate || includePrivate)) {
        methods.push({
          name: member.name.getText(),
          signature: this.getMethodSignature(member),
          description: this.extractJSDocComment(member),
          parameters: this.extractParameters(member),
          returns: this.extractReturnType(member),
          access: isPrivate ? 'private' : 'public'
        });
      }
      
      if (ts.isPropertyDeclaration(member) && member.name && (!isPrivate || includePrivate)) {
        properties.push({
          name: member.name.getText(),
          type: this.getTypeString(member.type),
          description: this.extractJSDocComment(member),
          access: isPrivate ? 'private' : 'public'
        });
      }
    }

    return {
      name: node.name!.getText(),
      type: 'class',
      description: this.extractJSDocComment(node),
      methods,
      properties
    };
  }

  private createInterfaceItem(node: ts.InterfaceDeclaration): ExportedItem {
    const properties: Property[] = [];

    for (const member of node.members) {
      if (ts.isPropertySignature(member) && member.name) {
        properties.push({
          name: member.name.getText(),
          type: this.getTypeString(member.type),
          description: this.extractJSDocComment(member),
          optional: !!member.questionToken
        });
      }
    }

    return {
      name: node.name.getText(),
      type: 'interface',
      description: this.extractJSDocComment(node),
      properties
    };
  }

  private createTypeItem(node: ts.TypeAliasDeclaration): ExportedItem {
    return {
      name: node.name.getText(),
      type: 'type',
      signature: this.getTypeString(node.type),
      description: this.extractJSDocComment(node)
    };
  }

  private createConstantItem(node: ts.VariableDeclaration): ExportedItem {
    return {
      name: node.name.getText(),
      type: 'constant',
      signature: this.getTypeString(node.type),
      description: this.extractJSDocComment(node.parent?.parent as ts.Node)
    };
  }

  private createEnumItem(node: ts.EnumDeclaration): ExportedItem {
    return {
      name: node.name.getText(),
      type: 'enum',
      description: this.extractJSDocComment(node)
    };
  }

  private getFunctionSignature(node: ts.FunctionDeclaration | ts.MethodDeclaration): string {
    const params = node.parameters.map(p => {
      const name = p.name.getText();
      const type = p.type ? `: ${this.getTypeString(p.type)}` : '';
      const optional = p.questionToken ? '?' : '';
      return `${name}${optional}${type}`;
    }).join(', ');
    
    const returnType = node.type ? `: ${this.getTypeString(node.type)}` : '';
    return `(${params})${returnType}`;
  }

  private getMethodSignature(node: ts.MethodDeclaration): string {
    return this.getFunctionSignature(node);
  }

  private extractParameters(node: ts.FunctionDeclaration | ts.MethodDeclaration): Parameter[] {
    return node.parameters.map(p => ({
      name: p.name.getText(),
      type: p.type ? this.getTypeString(p.type) : 'any',
      optional: !!p.questionToken,
      defaultValue: p.initializer?.getText(),
      description: this.extractParameterComment(node, p.name.getText())
    }));
  }

  private extractReturnType(node: ts.FunctionDeclaration | ts.MethodDeclaration): ReturnValue | undefined {
    if (node.type) {
      return {
        type: this.getTypeString(node.type),
        description: this.extractReturnComment(node)
      };
    }
    return undefined;
  }

  private getTypeString(type: ts.TypeNode | undefined): string {
    if (!type) return 'any';
    return type.getText();
  }

  private extractJSDocComment(node: ts.Node): string | undefined {
    const jsDoc = (node as any).jsDoc;
    if (jsDoc && jsDoc.length > 0) {
      return jsDoc[0].comment?.toString();
    }
    return undefined;
  }

  private extractParameterComment(node: ts.Node, paramName: string): string | undefined {
    const jsDoc = (node as any).jsDoc;
    if (jsDoc && jsDoc.length > 0) {
      const tags = jsDoc[0].tags;
      if (tags) {
        const paramTag = tags.find((tag: any) => 
          tag.kind === ts.SyntaxKind.JSDocParameterTag && 
          tag.name?.getText() === paramName
        );
        return paramTag?.comment?.toString();
      }
    }
    return undefined;
  }

  private extractReturnComment(node: ts.Node): string | undefined {
    const jsDoc = (node as any).jsDoc;
    if (jsDoc && jsDoc.length > 0) {
      const tags = jsDoc[0].tags;
      if (tags) {
        const returnTag = tags.find((tag: any) => tag.kind === ts.SyntaxKind.JSDocReturnTag);
        return returnTag?.comment?.toString();
      }
    }
    return undefined;
  }

  private extractDependencies(content: string): string[] {
    const dependencies: Set<string> = new Set();
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
    const examplePattern = /@example\s*([\s\S]*?)(?=@\w+|\*\/)/g;
    
    let match;
    while ((match = examplePattern.exec(content)) !== null) {
      const exampleText = match[1].trim();
      if (exampleText) {
        examples.push({
          title: 'Example',
          code: exampleText
        });
      }
    }

    return examples;
  }

  private extractDescription(content: string): string | undefined {
    const fileCommentPattern = /\/\*\*\s*([\s\S]*?)\*\//;
    const match = content.match(fileCommentPattern);
    
    if (match) {
      return match[1]
        .split('\n')
        .map(line => line.replace(/^\s*\*\s?/, '').trim())
        .filter(line => line && !line.startsWith('@'))
        .join('\n')
        .trim();
    }

    return undefined;
  }

  private async generateMetadata(content: string, filePath: string): Promise<Metadata> {
    const stats = await fs.stat(filePath);
    const lines = content.split('\n');
    const linesOfCode = lines.filter(line => line.trim() && !line.trim().startsWith('//')).length;
    
    // Simple complexity calculation
    const complexity = this.calculateComplexity(content);

    return {
      lastModified: stats.mtime.toISOString(),
      fileSize: stats.size,
      linesOfCode,
      complexity
    };
  }

  private calculateComplexity(content: string): number {
    let complexity = 1;
    const patterns = [
      /if\s*\(/g,
      /for\s*\(/g,
      /while\s*\(/g,
      /case\s+/g,
      /catch\s*\(/g,
      /\?\s*[^:]+:/g,
      /&&/g,
      /\|\|/g
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
    const counts = {
      function: 0,
      class: 0,
      interface: 0,
      type: 0,
      constant: 0,
      enum: 0
    };

    for (const item of exports) {
      counts[item.type]++;
    }

    const parts: string[] = [];
    if (counts.function > 0) parts.push(`${counts.function} functions`);
    if (counts.class > 0) parts.push(`${counts.class} classes`);
    if (counts.interface > 0) parts.push(`${counts.interface} interfaces`);
    if (counts.type > 0) parts.push(`${counts.type} type aliases`);
    if (counts.constant > 0) parts.push(`${counts.constant} constants`);
    if (counts.enum > 0) parts.push(`${counts.enum} enums`);

    return `Module exports: ${parts.join(', ') || 'none'}`;
  }

  private formatDocumentation(doc: Documentation, format: string): string {
    switch (format) {
      case 'markdown':
        return this.formatAsMarkdown(doc);
      case 'jsdoc':
        return this.formatAsJSDoc(doc);
      case 'api-json':
        return JSON.stringify(doc, null, 2);
      default:
        return this.formatAsMarkdown(doc);
    }
  }

  private formatAsMarkdown(doc: Documentation): string {
    let md = `# ${doc.summary}\n\n`;
    
    if (doc.description) {
      md += `${doc.description}\n\n`;
    }

    if (doc.exports.length > 0) {
      md += `## API Reference\n\n`;
      
      for (const item of doc.exports) {
        md += `### ${item.name}\n\n`;
        md += `**Type:** \`${item.type}\`\n\n`;
        
        if (item.description) {
          md += `${item.description}\n\n`;
        }
        
        if (item.signature) {
          md += `**Signature:** \`${item.signature}\`\n\n`;
        }
        
        if (item.parameters && item.parameters.length > 0) {
          md += `**Parameters:**\n`;
          for (const param of item.parameters) {
            md += `- \`${param.name}\` (${param.type})${param.optional ? ' *optional*' : ''}: ${param.description || ''}\n`;
          }
          md += '\n';
        }
        
        if (item.returns) {
          md += `**Returns:** \`${item.returns.type}\` ${item.returns.description || ''}\n\n`;
        }
      }
    }

    if (doc.examples && doc.examples.length > 0) {
      md += `## Examples\n\n`;
      for (const example of doc.examples) {
        md += `### ${example.title}\n\n`;
        md += `\`\`\`typescript\n${example.code}\n\`\`\`\n\n`;
        if (example.description) {
          md += `${example.description}\n\n`;
        }
      }
    }

    if (doc.dependencies.length > 0) {
      md += `## Dependencies\n\n`;
      for (const dep of doc.dependencies) {
        md += `- \`${dep}\`\n`;
      }
      md += '\n';
    }

    return md;
  }

  private formatAsJSDoc(doc: Documentation): string {
    let jsdoc = `/**\n * ${doc.summary}\n`;
    
    if (doc.description) {
      jsdoc += ` * \n * ${doc.description.replace(/\n/g, '\n * ')}\n`;
    }
    
    jsdoc += ` */\n`;
    
    return jsdoc;
  }

  private getOutputPath(inputFile: string, outputDir: string, format: string): string {
    const basename = path.basename(inputFile, path.extname(inputFile));
    const extension = format === 'api-json' ? 'json' : 'md';
    return path.join(outputDir, `${basename}.${extension}`);
  }

  private generateSummary(results: DocumentationResult[]): string {
    let summary = `Generated documentation for ${results.length} file(s)\n\n`;
    
    let totalExports = 0;
    const formats = new Set<string>();
    let written = 0;

    for (const result of results) {
      totalExports += result.documentation.exports.length;
      formats.add(result.format);
      if (result.written) written++;
    }

    summary += `Total exports documented: ${totalExports}\n`;
    summary += `Format(s): ${Array.from(formats).join(', ')}\n`;
    if (written > 0) {
      summary += `Files written: ${written}\n`;
    }

    return summary;
  }
}