/**
 * Document Command for ae-framework
 * Intelligent documentation generation
 */

import { CommandHandler, CommandResult, CommandContext } from '../slash-command-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';

export class DocumentCommand {
  name = '/ae:document';
  description = 'Intelligent documentation generation';
  category = 'utility' as const;
  usage = '/ae:document <file|directory> [--format <markdown|jsdoc|api>]';
  aliases = ['/document', '/docs', '/doc'];

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a file or directory to document'
      };
    }

    const target = args[0];
    const options = this.parseOptions(args.slice(1));
    const format = options.format || 'markdown';

    try {
      const documentation = await this.generateDocumentation(target, format, context);
      
      if (options.output) {
        await this.saveDocumentation(documentation, options.output);
        return {
          success: true,
          message: `Documentation saved to ${options.output}`,
          data: documentation
        };
      }

      return {
        success: true,
        message: documentation.content,
        data: documentation
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Documentation generation failed: ${error.message}`
      };
    }
  }

  private async generateDocumentation(
    target: string,
    format: string,
    context: CommandContext
  ): Promise<Documentation> {
    const fullPath = path.resolve(context.projectRoot, target);
    const stats = await fs.stat(fullPath);
    
    if (stats.isDirectory()) {
      return this.documentDirectory(fullPath, format);
    } else {
      return this.documentFile(fullPath, format);
    }
  }

  private async documentFile(filePath: string, format: string): Promise<Documentation> {
    const content = await fs.readFile(filePath, 'utf-8');
    const ext = path.extname(filePath);
    const fileName = path.basename(filePath);

    const analysis = this.analyzeCode(content, ext);
    
    let documentation: Documentation = {
      title: fileName,
      type: 'file',
      format,
      content: '',
      metadata: {
        path: filePath,
        generated: new Date().toISOString(),
        stats: analysis.stats
      }
    };

    switch (format) {
      case 'markdown':
        documentation.content = this.generateMarkdownDoc(fileName, analysis);
        break;
      case 'jsdoc':
        documentation.content = this.generateJSDocComments(analysis);
        break;
      case 'api':
        documentation.content = this.generateAPIDoc(fileName, analysis);
        break;
      default:
        documentation.content = this.generateMarkdownDoc(fileName, analysis);
    }

    return documentation;
  }

  private async documentDirectory(dirPath: string, format: string): Promise<Documentation> {
    const files = await this.scanDirectory(dirPath);
    const documentations: Documentation[] = [];

    for (const file of files) {
      const doc = await this.documentFile(file, format);
      documentations.push(doc);
    }

    return this.combineDocumentations(documentations, dirPath, format);
  }

  private analyzeCode(content: string, ext: string): CodeAnalysis {
    const analysis: CodeAnalysis = {
      classes: this.extractClasses(content),
      functions: this.extractFunctions(content),
      interfaces: this.extractInterfaces(content),
      imports: this.extractImports(content),
      exports: this.extractExports(content),
      constants: this.extractConstants(content),
      stats: {
        lines: content.split('\n').length,
        classes: 0,
        functions: 0,
        interfaces: 0
      }
    };

    analysis.stats.classes = analysis.classes.length;
    analysis.stats.functions = analysis.functions.length;
    analysis.stats.interfaces = analysis.interfaces.length;

    return analysis;
  }

  private extractClasses(content: string): ClassInfo[] {
    const classes: ClassInfo[] = [];
    const classRegex = /(?:export\s+)?class\s+(\w+)(?:\s+extends\s+(\w+))?(?:\s+implements\s+([\w\s,]+))?\s*\{/g;
    
    let match;
    while ((match = classRegex.exec(content)) !== null) {
      const className = match[1];
      const extendsClass = match[2];
      const implementsList = match[3]?.split(',').map(s => s.trim());
      
      const classBody = this.extractClassBody(content, match.index);
      const methods = this.extractClassMethods(classBody);
      const properties = this.extractClassProperties(classBody);
      
      classes.push({
        name: className,
        extends: extendsClass,
        implements: implementsList,
        methods,
        properties,
        description: this.extractComment(content, match.index)
      });
    }

    return classes;
  }

  private extractFunctions(content: string): FunctionInfo[] {
    const functions: FunctionInfo[] = [];
    const functionRegex = /(?:export\s+)?(?:async\s+)?function\s+(\w+)\s*\(([^)]*)\)(?:\s*:\s*([^{]+))?\s*\{/g;
    const arrowRegex = /(?:export\s+)?(?:const|let)\s+(\w+)\s*=\s*(?:async\s+)?\(([^)]*)\)(?:\s*:\s*([^=]+))?\s*=>/g;
    
    let match;
    
    // Traditional functions
    while ((match = functionRegex.exec(content)) !== null) {
      functions.push({
        name: match[1],
        parameters: this.parseParameters(match[2]),
        returnType: match[3]?.trim(),
        isAsync: content.substring(match.index - 10, match.index).includes('async'),
        description: this.extractComment(content, match.index)
      });
    }
    
    // Arrow functions
    while ((match = arrowRegex.exec(content)) !== null) {
      functions.push({
        name: match[1],
        parameters: this.parseParameters(match[2]),
        returnType: match[3]?.trim(),
        isAsync: content.substring(match.index - 10, match.index).includes('async'),
        description: this.extractComment(content, match.index)
      });
    }

    return functions;
  }

  private extractInterfaces(content: string): InterfaceInfo[] {
    const interfaces: InterfaceInfo[] = [];
    const interfaceRegex = /(?:export\s+)?interface\s+(\w+)(?:\s+extends\s+([\w\s,]+))?\s*\{/g;
    
    let match;
    while ((match = interfaceRegex.exec(content)) !== null) {
      const interfaceName = match[1];
      const extends_ = match[2]?.split(',').map(s => s.trim());
      
      const interfaceBody = this.extractBlockBody(content, match.index);
      const properties = this.extractInterfaceProperties(interfaceBody);
      
      interfaces.push({
        name: interfaceName,
        extends: extends_,
        properties,
        description: this.extractComment(content, match.index)
      });
    }

    return interfaces;
  }

  private extractImports(content: string): string[] {
    const imports: string[] = [];
    const importRegex = /import\s+(?:{[^}]+}|\*\s+as\s+\w+|\w+)\s+from\s+['"]([^'"]+)['"]/g;
    
    let match;
    while ((match = importRegex.exec(content)) !== null) {
      imports.push(match[1]);
    }

    return imports;
  }

  private extractExports(content: string): string[] {
    const exports: string[] = [];
    const exportRegex = /export\s+(?:default\s+)?(?:class|function|const|let|var|interface|type)\s+(\w+)/g;
    
    let match;
    while ((match = exportRegex.exec(content)) !== null) {
      exports.push(match[1]);
    }

    return exports;
  }

  private extractConstants(content: string): ConstantInfo[] {
    const constants: ConstantInfo[] = [];
    const constRegex = /(?:export\s+)?const\s+([A-Z_]+)\s*(?::\s*([^=]+))?\s*=\s*([^;]+);/g;
    
    let match;
    while ((match = constRegex.exec(content)) !== null) {
      constants.push({
        name: match[1],
        type: match[2]?.trim(),
        value: match[3].trim(),
        description: this.extractComment(content, match.index)
      });
    }

    return constants;
  }

  private extractClassBody(content: string, startIndex: number): string {
    let braceCount = 0;
    let inClass = false;
    let endIndex = startIndex;
    
    for (let i = startIndex; i < content.length; i++) {
      if (content[i] === '{') {
        braceCount++;
        inClass = true;
      } else if (content[i] === '}') {
        braceCount--;
        if (inClass && braceCount === 0) {
          endIndex = i;
          break;
        }
      }
    }
    
    return content.substring(startIndex, endIndex + 1);
  }

  private extractBlockBody(content: string, startIndex: number): string {
    return this.extractClassBody(content, startIndex);
  }

  private extractClassMethods(classBody: string): MethodInfo[] {
    const methods: MethodInfo[] = [];
    const methodRegex = /(?:public|private|protected)?\s*(?:static\s+)?(?:async\s+)?(\w+)\s*\(([^)]*)\)(?:\s*:\s*([^{]+))?\s*\{/g;
    
    let match;
    while ((match = methodRegex.exec(classBody)) !== null) {
      if (match[1] !== 'constructor') {
        methods.push({
          name: match[1],
          parameters: this.parseParameters(match[2]),
          returnType: match[3]?.trim(),
          visibility: this.extractVisibility(classBody, match.index),
          isStatic: classBody.substring(match.index - 20, match.index).includes('static'),
          isAsync: classBody.substring(match.index - 20, match.index).includes('async')
        });
      }
    }

    return methods;
  }

  private extractClassProperties(classBody: string): PropertyInfo[] {
    const properties: PropertyInfo[] = [];
    const propertyRegex = /(?:public|private|protected)?\s*(?:readonly\s+)?(\w+)(?:\?)?(?:\s*:\s*([^;=]+))?(?:\s*=\s*([^;]+))?;/g;
    
    let match;
    while ((match = propertyRegex.exec(classBody)) !== null) {
      properties.push({
        name: match[1],
        type: match[2]?.trim(),
        defaultValue: match[3]?.trim(),
        visibility: this.extractVisibility(classBody, match.index),
        isReadonly: classBody.substring(match.index - 20, match.index).includes('readonly'),
        isOptional: classBody.substring(match.index, match.index + 50).includes('?')
      });
    }

    return properties;
  }

  private extractInterfaceProperties(interfaceBody: string): PropertyInfo[] {
    const properties: PropertyInfo[] = [];
    const propertyRegex = /(\w+)(\?)?(?:\s*:\s*([^;]+));/g;
    
    let match;
    while ((match = propertyRegex.exec(interfaceBody)) !== null) {
      properties.push({
        name: match[1],
        type: match[3]?.trim(),
        isOptional: match[2] === '?'
      });
    }

    return properties;
  }

  private parseParameters(params: string): ParameterInfo[] {
    if (!params.trim()) return [];
    
    return params.split(',').map(param => {
      const parts = param.trim().split(':');
      const name = parts[0].trim().replace('?', '');
      const type = parts[1]?.trim();
      const isOptional = param.includes('?');
      const hasDefault = param.includes('=');
      
      return { name, type, isOptional, hasDefault };
    });
  }

  private extractVisibility(content: string, index: number): 'public' | 'private' | 'protected' {
    const before = content.substring(Math.max(0, index - 20), index);
    if (before.includes('private')) return 'private';
    if (before.includes('protected')) return 'protected';
    return 'public';
  }

  private extractComment(content: string, index: number): string {
    // Look for JSDoc comment before the declaration
    const before = content.substring(Math.max(0, index - 500), index);
    const jsdocMatch = before.match(/\/\*\*([^*]|\*(?!\/))*\*\/\s*$/);
    
    if (jsdocMatch) {
      return this.cleanComment(jsdocMatch[0]);
    }
    
    // Look for single-line comment
    const lineMatch = before.match(/\/\/\s*(.+)\s*$/);
    if (lineMatch) {
      return lineMatch[1].trim();
    }
    
    return '';
  }

  private cleanComment(comment: string): string {
    return comment
      .replace(/\/\*\*|\*\//g, '')
      .replace(/^\s*\*\s?/gm, '')
      .trim();
  }

  private generateMarkdownDoc(fileName: string, analysis: CodeAnalysis): string {
    let doc = `# ${fileName}\n\n`;
    
    // Add file statistics
    doc += `## Statistics\n`;
    doc += `- Lines: ${analysis.stats.lines}\n`;
    doc += `- Classes: ${analysis.stats.classes}\n`;
    doc += `- Functions: ${analysis.stats.functions}\n`;
    doc += `- Interfaces: ${analysis.stats.interfaces}\n\n`;
    
    // Document imports
    if (analysis.imports.length > 0) {
      doc += `## Dependencies\n`;
      for (const imp of analysis.imports) {
        doc += `- ${imp}\n`;
      }
      doc += '\n';
    }
    
    // Document interfaces
    if (analysis.interfaces.length > 0) {
      doc += `## Interfaces\n\n`;
      for (const iface of analysis.interfaces) {
        doc += `### ${iface.name}\n`;
        if (iface.description) doc += `${iface.description}\n\n`;
        if (iface.extends) doc += `Extends: ${iface.extends.join(', ')}\n\n`;
        
        doc += `#### Properties\n`;
        for (const prop of iface.properties) {
          doc += `- **${prop.name}**${prop.isOptional ? '?' : ''}: \`${prop.type || 'any'}\`\n`;
        }
        doc += '\n';
      }
    }
    
    // Document classes
    if (analysis.classes.length > 0) {
      doc += `## Classes\n\n`;
      for (const cls of analysis.classes) {
        doc += `### ${cls.name}\n`;
        if (cls.description) doc += `${cls.description}\n\n`;
        if (cls.extends) doc += `Extends: ${cls.extends}\n`;
        if (cls.implements) doc += `Implements: ${cls.implements.join(', ')}\n\n`;
        
        if (cls.properties.length > 0) {
          doc += `#### Properties\n`;
          for (const prop of cls.properties) {
            doc += `- **${prop.name}** (\`${prop.visibility}\`): \`${prop.type || 'any'}\``;
            if (prop.defaultValue) doc += ` = \`${prop.defaultValue}\``;
            doc += '\n';
          }
          doc += '\n';
        }
        
        if (cls.methods.length > 0) {
          doc += `#### Methods\n`;
          for (const method of cls.methods) {
            doc += `- **${method.name}**(${this.formatParameters(method.parameters)}): \`${method.returnType || 'void'}\``;
            if (method.isAsync) doc += ` *(async)*`;
            if (method.isStatic) doc += ` *(static)*`;
            doc += '\n';
          }
          doc += '\n';
        }
      }
    }
    
    // Document functions
    if (analysis.functions.length > 0) {
      doc += `## Functions\n\n`;
      for (const func of analysis.functions) {
        doc += `### ${func.name}\n`;
        if (func.description) doc += `${func.description}\n\n`;
        doc += `\`\`\`typescript\n`;
        doc += `${func.isAsync ? 'async ' : ''}function ${func.name}(${this.formatParameters(func.parameters)}): ${func.returnType || 'void'}\n`;
        doc += `\`\`\`\n\n`;
      }
    }
    
    // Document constants
    if (analysis.constants.length > 0) {
      doc += `## Constants\n\n`;
      for (const constant of analysis.constants) {
        doc += `- **${constant.name}**: \`${constant.type || 'any'}\` = \`${constant.value}\`\n`;
        if (constant.description) doc += `  ${constant.description}\n`;
      }
      doc += '\n';
    }
    
    // Document exports
    if (analysis.exports.length > 0) {
      doc += `## Exports\n`;
      for (const exp of analysis.exports) {
        doc += `- ${exp}\n`;
      }
    }
    
    return doc;
  }

  private generateJSDocComments(analysis: CodeAnalysis): string {
    let jsdoc = '';
    
    // Generate JSDoc for classes
    for (const cls of analysis.classes) {
      jsdoc += `/**\n`;
      jsdoc += ` * ${cls.description || cls.name}\n`;
      if (cls.extends) jsdoc += ` * @extends ${cls.extends}\n`;
      if (cls.implements) {
        for (const impl of cls.implements) {
          jsdoc += ` * @implements ${impl}\n`;
        }
      }
      jsdoc += ` */\n\n`;
      
      // Methods
      for (const method of cls.methods) {
        jsdoc += `/**\n`;
        jsdoc += ` * ${method.name} method\n`;
        for (const param of method.parameters) {
          jsdoc += ` * @param {${param.type || '*'}} ${param.name}${param.isOptional ? ' - Optional' : ''}\n`;
        }
        if (method.returnType) {
          jsdoc += ` * @returns {${method.returnType}}\n`;
        }
        jsdoc += ` */\n\n`;
      }
    }
    
    // Generate JSDoc for functions
    for (const func of analysis.functions) {
      jsdoc += `/**\n`;
      jsdoc += ` * ${func.description || func.name}\n`;
      for (const param of func.parameters) {
        jsdoc += ` * @param {${param.type || '*'}} ${param.name}${param.isOptional ? ' - Optional' : ''}\n`;
      }
      if (func.returnType) {
        jsdoc += ` * @returns {${func.returnType}}\n`;
      }
      if (func.isAsync) {
        jsdoc += ` * @async\n`;
      }
      jsdoc += ` */\n\n`;
    }
    
    return jsdoc;
  }

  private generateAPIDoc(fileName: string, analysis: CodeAnalysis): string {
    const api: any = {
      name: fileName,
      version: '1.0.0',
      description: `API documentation for ${fileName}`,
      classes: analysis.classes,
      functions: analysis.functions,
      interfaces: analysis.interfaces,
      exports: analysis.exports
    };
    
    return JSON.stringify(api, null, 2);
  }

  private formatParameters(params: ParameterInfo[]): string {
    return params.map(p => {
      let param = p.name;
      if (p.isOptional) param += '?';
      if (p.type) param += `: ${p.type}`;
      return param;
    }).join(', ');
  }

  private async scanDirectory(dirPath: string): Promise<string[]> {
    const files: string[] = [];
    const entries = await fs.readdir(dirPath, { withFileTypes: true });
    
    for (const entry of entries) {
      const fullPath = path.join(dirPath, entry.name);
      if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
        const subFiles = await this.scanDirectory(fullPath);
        files.push(...subFiles);
      } else if (entry.isFile() && this.shouldDocument(fullPath)) {
        files.push(fullPath);
      }
    }
    
    return files;
  }

  private shouldDocument(filePath: string): boolean {
    const ext = path.extname(filePath);
    return ['.ts', '.js', '.tsx', '.jsx'].includes(ext);
  }

  private combineDocumentations(
    docs: Documentation[],
    dirPath: string,
    format: string
  ): Documentation {
    const dirName = path.basename(dirPath);
    let combined = `# ${dirName} Documentation\n\n`;
    combined += `Generated: ${new Date().toISOString()}\n\n`;
    combined += `## Table of Contents\n\n`;
    
    // Generate TOC
    for (const doc of docs) {
      const relativePath = path.relative(dirPath, doc.metadata?.path || '');
      combined += `- [${relativePath}](#${relativePath.replace(/[\/\\.]/g, '-')})\n`;
    }
    combined += '\n---\n\n';
    
    // Add individual documentations
    for (const doc of docs) {
      const relativePath = path.relative(dirPath, doc.metadata?.path || '');
      combined += `## ${relativePath}\n\n`;
      combined += doc.content;
      combined += '\n---\n\n';
    }
    
    return {
      title: dirName,
      type: 'directory',
      format,
      content: combined,
      metadata: {
        path: dirPath,
        generated: new Date().toISOString(),
        fileCount: docs.length
      }
    };
  }

  private async saveDocumentation(doc: Documentation, outputPath: string): Promise<void> {
    const dir = path.dirname(outputPath);
    await fs.mkdir(dir, { recursive: true });
    await fs.writeFile(outputPath, doc.content, 'utf-8');
  }

  private parseOptions(args: string[]): Record<string, any> {
    const options: Record<string, any> = {};
    for (let i = 0; i < args.length; i++) {
      if (args[i].startsWith('--')) {
        const key = args[i].slice(2);
        const value = args[i + 1] && !args[i + 1].startsWith('--') ? args[i + 1] : true;
        options[key] = value;
        if (value !== true) i++;
      }
    }
    return options;
  }
}

// Type definitions
interface Documentation {
  title: string;
  type: 'file' | 'directory';
  format: string;
  content: string;
  metadata?: {
    path: string;
    generated: string;
    stats?: any;
    fileCount?: number;
  };
}

interface CodeAnalysis {
  classes: ClassInfo[];
  functions: FunctionInfo[];
  interfaces: InterfaceInfo[];
  imports: string[];
  exports: string[];
  constants: ConstantInfo[];
  stats: {
    lines: number;
    classes: number;
    functions: number;
    interfaces: number;
  };
}

interface ClassInfo {
  name: string;
  extends?: string;
  implements?: string[];
  methods: MethodInfo[];
  properties: PropertyInfo[];
  description?: string;
}

interface FunctionInfo {
  name: string;
  parameters: ParameterInfo[];
  returnType?: string;
  isAsync: boolean;
  description?: string;
}

interface InterfaceInfo {
  name: string;
  extends?: string[];
  properties: PropertyInfo[];
  description?: string;
}

interface MethodInfo {
  name: string;
  parameters: ParameterInfo[];
  returnType?: string;
  visibility: 'public' | 'private' | 'protected';
  isStatic: boolean;
  isAsync: boolean;
}

interface PropertyInfo {
  name: string;
  type?: string;
  defaultValue?: string;
  visibility?: 'public' | 'private' | 'protected';
  isReadonly?: boolean;
  isOptional?: boolean;
}

interface ParameterInfo {
  name: string;
  type?: string;
  isOptional: boolean;
  hasDefault?: boolean;
}

interface ConstantInfo {
  name: string;
  type?: string;
  value: string;
  description?: string;
}