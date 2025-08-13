/**
 * Unified Document Command for ae-framework
 * Generates comprehensive documentation with unified interface
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import * as ts from 'typescript';
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { 
  DocumentationResult, 
  AnalysisTarget, 
  DocumentationOptions,
  ExportedItem,
  Parameter,
  ReturnValue,
  Example
} from './types.js';

export class UnifiedDocumentCommand extends BaseExtendedCommand {
  constructor() {
    super({
      name: '/ae:document',
      description: 'Generate comprehensive documentation',
      usage: '/ae:document <file|directory> [--format=markdown|jsdoc|api-json] [--output=path] [--validate]',
      aliases: ['/document', '/a:document'],
      category: 'utility'
    });
  }

  protected validateArgs(args: string[]): { isValid: boolean; message?: string } {
    if (args.length === 0) {
      return {
        isValid: false,
        message: 'Please specify a file or directory to document'
      };
    }
    return { isValid: true };
  }

  protected parseOptions(args: string[]): DocumentationOptions {
    const baseOptions = super.parseOptions(args);
    
    return {
      ...baseOptions,
      format: (args.find(arg => arg.startsWith('--format='))?.split('=')[1] as any) || 'markdown',
      includePrivate: args.includes('--include-private'),
      includeExamples: args.includes('--include-examples'),
      template: args.find(arg => arg.startsWith('--template='))?.split('=')[1]
    };
  }

  protected async execute(
    args: string[], 
    options: DocumentationOptions, 
    context: CommandContext
  ): Promise<ExtendedCommandResult<DocumentationResult>> {
    const target = args[0];
    const fullPath = path.resolve(context.projectRoot, target);
    
    try {
      const stats = await fs.stat(fullPath);
      const analysisTarget: AnalysisTarget = {
        path: fullPath,
        type: stats.isDirectory() ? 'directory' : 'file'
      };

      const result = await this.generateDocumentation(analysisTarget, options);
      const summary = this.generateSummary(result);

      return {
        success: true,
        message: summary,
        data: result,
        metrics: {
          executionTime: 0, // Will be set by base class
          filesProcessed: result.metrics.files,
          confidence: this.calculateDocumentationCompleteness(result)
        }
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Documentation generation failed: ${error.message}`,
        metrics: {
          executionTime: 0,
          filesProcessed: 0
        }
      };
    }
  }

  private async generateDocumentation(target: AnalysisTarget, options: DocumentationOptions): Promise<DocumentationResult> {
    const startTime = Date.now();
    
    let files: string[] = [];
    if (target.type === 'directory') {
      files = await this.findSourceFiles(target.path);
    } else {
      files = [target.path];
    }

    const allExports: ExportedItem[] = [];
    const allExamples: Example[] = [];
    const dependencies = new Set<string>();
    let totalLines = 0;
    let outputPath: string | undefined;

    // Process each file
    for (const file of files) {
      const fileDoc = await this.documentFile(file, options);
      
      allExports.push(...fileDoc.exports);
      allExamples.push(...fileDoc.examples);
      fileDoc.dependencies.forEach(dep => dependencies.add(dep));
      totalLines += fileDoc.fileMetrics.linesOfCode;

      // Write individual file documentation if requested
      if (options.output) {
        const fileOutputPath = this.getOutputPath(file, options.output, options.format || 'markdown');
        const formatted = this.formatDocumentation(fileDoc, options.format || 'markdown');
        await fs.writeFile(fileOutputPath, formatted);
        outputPath = options.output;
      }
    }

    // Calculate coverage
    const coverage = this.calculateDocumentationCoverage(allExports);

    return {
      target,
      summary: this.createDocumentationSummary(allExports.length, files.length, coverage),
      issues: [], // Documentation generation doesn't typically produce issues
      suggestions: this.generateDocumentationSuggestions(allExports, coverage),
      metrics: {
        lines: totalLines,
        files: files.length,
        coverage
      },
      metadata: {
        timestamp: new Date().toISOString(),
        commandType: 'document',
        processingTime: Date.now() - startTime
      },
      documentation: {
        exports: allExports,
        examples: allExamples,
        dependencies: Array.from(dependencies),
        coverage
      },
      format: options.format || 'markdown',
      outputPath
    };
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

  private async documentFile(filePath: string, options: DocumentationOptions): Promise<{
    exports: ExportedItem[];
    examples: Example[];
    dependencies: string[];
    fileMetrics: { linesOfCode: number };
  }> {
    const content = await fs.readFile(filePath, 'utf-8');
    const lines = content.split('\n');
    
    // Parse TypeScript if applicable
    let exports: ExportedItem[] = [];
    if (filePath.endsWith('.ts')) {
      exports = await this.parseTypeScriptFile(content, filePath, options.includePrivate || false);
    } else {
      exports = this.parseJavaScriptFile(content, filePath);
    }

    const examples = this.extractExamples(content);
    const dependencies = this.extractDependencies(content);

    return {
      exports,
      examples,
      dependencies,
      fileMetrics: {
        linesOfCode: lines.filter(line => line.trim() && !line.trim().startsWith('//')).length
      }
    };
  }

  private async parseTypeScriptFile(content: string, filePath: string, includePrivate: boolean): Promise<ExportedItem[]> {
    const sourceFile = ts.createSourceFile(
      filePath,
      content,
      ts.ScriptTarget.Latest,
      true
    );

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

  private parseJavaScriptFile(content: string, filePath: string): ExportedItem[] {
    const exports: ExportedItem[] = [];
    const lines = content.split('\n');

    // Simple regex-based parsing for JavaScript
    lines.forEach((line, index) => {
      // Function declarations
      const funcMatch = line.match(/(?:export\s+)?(?:function\s+|const\s+\w+\s*=\s*(?:async\s+)?function\s*|const\s+\w+\s*=\s*(?:async\s+)?\()/);
      if (funcMatch) {
        const nameMatch = line.match(/(?:function\s+(\w+)|const\s+(\w+)\s*=)/);
        if (nameMatch) {
          exports.push({
            name: nameMatch[1] || nameMatch[2],
            type: 'function',
            signature: line.trim(),
            description: this.extractJSDocFromLines(lines, index)
          });
        }
      }

      // Class declarations
      const classMatch = line.match(/(?:export\s+)?class\s+(\w+)/);
      if (classMatch) {
        exports.push({
          name: classMatch[1],
          type: 'class',
          description: this.extractJSDocFromLines(lines, index)
        });
      }

      // Constants
      const constMatch = line.match(/(?:export\s+)?const\s+(\w+)\s*=/);
      if (constMatch && !line.includes('function') && !line.includes('=>')) {
        exports.push({
          name: constMatch[1],
          type: 'constant',
          signature: line.trim(),
          description: this.extractJSDocFromLines(lines, index)
        });
      }
    });

    return exports;
  }

  private hasPrivateModifier(node: ts.Node): boolean {
    return (node as any).modifiers?.some((mod: any) => mod.kind === ts.SyntaxKind.PrivateKeyword) ?? false;
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
    return {
      name: node.name!.getText(),
      type: 'class',
      description: this.extractJSDocComment(node)
    };
  }

  private createInterfaceItem(node: ts.InterfaceDeclaration): ExportedItem {
    return {
      name: node.name.getText(),
      type: 'interface',
      description: this.extractJSDocComment(node)
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

  private getFunctionSignature(node: ts.FunctionDeclaration): string {
    const params = node.parameters.map(p => {
      const name = p.name.getText();
      const type = p.type ? `: ${this.getTypeString(p.type)}` : '';
      const optional = p.questionToken ? '?' : '';
      return `${name}${optional}${type}`;
    }).join(', ');
    
    const returnType = node.type ? `: ${this.getTypeString(node.type)}` : '';
    return `(${params})${returnType}`;
  }

  private extractParameters(node: ts.FunctionDeclaration): Parameter[] {
    return node.parameters.map(p => ({
      name: p.name.getText(),
      type: p.type ? this.getTypeString(p.type) : 'any',
      optional: !!p.questionToken,
      defaultValue: p.initializer?.getText(),
      description: this.extractParameterComment(node, p.name.getText())
    }));
  }

  private extractReturnType(node: ts.FunctionDeclaration): ReturnValue | undefined {
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

  private extractJSDocFromLines(lines: string[], lineIndex: number): string | undefined {
    // Look backwards for JSDoc comment
    let i = lineIndex - 1;
    while (i >= 0 && lines[i].trim() === '') i--;
    
    if (i >= 0 && lines[i].trim().endsWith('*/')) {
      const comment = [];
      while (i >= 0 && !lines[i].includes('/**')) {
        comment.unshift(lines[i]);
        i--;
      }
      if (i >= 0) {
        comment.unshift(lines[i]);
        return comment
          .join('\n')
          .replace(/\/\*\*|\*\/|\*\s?/g, '')
          .trim();
      }
    }
    return undefined;
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

  private calculateDocumentationCoverage(exports: ExportedItem[]): number {
    if (exports.length === 0) return 1.0;
    
    const documented = exports.filter(item => item.description && item.description.length > 0).length;
    return documented / exports.length;
  }

  private generateDocumentationSuggestions(exports: ExportedItem[], coverage: number) {
    const suggestions = [];
    
    if (coverage < 0.8) {
      suggestions.push({
        type: 'documentation-improvement',
        message: `Documentation coverage is ${(coverage * 100).toFixed(1)}%. Consider adding JSDoc comments to undocumented exports.`,
        priority: 'medium' as const,
        category: 'documentation'
      });
    }

    const functionsWithoutParams = exports.filter(item => 
      item.type === 'function' && 
      item.parameters && 
      item.parameters.some(param => !param.description)
    );

    if (functionsWithoutParams.length > 0) {
      suggestions.push({
        type: 'parameter-documentation',
        message: `${functionsWithoutParams.length} functions have undocumented parameters. Add @param tags for better documentation.`,
        priority: 'low' as const,
        category: 'documentation'
      });
    }

    return suggestions;
  }

  private formatDocumentation(doc: any, format: string): string {
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

  private formatAsMarkdown(doc: any): string {
    let md = `# ${doc.exports.length} Exports Found\n\n`;
    
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
      }
    }

    return md;
  }

  private formatAsJSDoc(doc: any): string {
    let jsdoc = `/**\n * Module with ${doc.exports.length} exports\n`;
    jsdoc += ` */\n`;
    return jsdoc;
  }

  private getOutputPath(inputFile: string, outputDir: string, format: string): string {
    const basename = path.basename(inputFile, path.extname(inputFile));
    const extension = format === 'api-json' ? 'json' : 'md';
    return path.join(outputDir, `${basename}.${extension}`);
  }

  private calculateDocumentationCompleteness(result: DocumentationResult): number {
    return result.documentation.coverage;
  }

  private createDocumentationSummary(exportCount: number, fileCount: number, coverage: number): string {
    return `Generated documentation for ${fileCount} file(s) with ${exportCount} exports (${(coverage * 100).toFixed(1)}% documented)`;
  }

  protected generateValidationClaim(data: DocumentationResult): string {
    return `Documentation completeness for ${data.target.path}: ${data.documentation.exports.length} exports documented at ${(data.documentation.coverage * 100).toFixed(1)}%`;
  }

  protected generateSummary(data: DocumentationResult): string {
    return data.summary;
  }
}