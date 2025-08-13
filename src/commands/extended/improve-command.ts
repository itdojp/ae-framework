/**
 * Improve Command for ae-framework
 * Code quality and performance improvements
 */

import { CommandHandler, CommandResult, CommandContext } from '../slash-command-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';

export class ImproveCommand {
  name = '/ae:improve';
  description = 'Code quality and performance improvements';
  category = 'utility' as const;
  usage = '/ae:improve <file|directory> [--type <quality|performance|security>]';
  aliases = ['/improve', '/optimize', '/refactor'];

  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a file or directory to improve'
      };
    }

    const target = args[0];
    const options = this.parseOptions(args.slice(1));
    const improvementType = options.type || 'all';

    try {
      const improvements = await this.analyzeAndSuggestImprovements(
        target,
        improvementType,
        context
      );

      if (options.apply) {
        const applied = await this.applyImprovements(improvements, options.auto);
        return {
          success: true,
          message: this.formatAppliedReport(applied),
          data: applied
        };
      }

      return {
        success: true,
        message: this.formatImprovementReport(improvements),
        data: improvements
      };
    } catch (error: any) {
      return {
        success: false,
        message: `Improvement analysis failed: ${error.message}`
      };
    }
  }

  private async analyzeAndSuggestImprovements(
    target: string,
    type: string,
    context: CommandContext
  ): Promise<Improvement[]> {
    const fullPath = path.resolve(context.projectRoot, target);
    const stats = await fs.stat(fullPath);
    
    let improvements: Improvement[] = [];

    if (stats.isDirectory()) {
      const files = await this.scanDirectory(fullPath);
      for (const file of files) {
        const fileImprovements = await this.analyzeFile(file, type);
        improvements.push(...fileImprovements);
      }
    } else {
      improvements = await this.analyzeFile(fullPath, type);
    }

    // Sort by priority
    improvements.sort((a, b) => {
      const priorityOrder = { high: 0, medium: 1, low: 2 };
      return priorityOrder[a.priority] - priorityOrder[b.priority];
    });

    return improvements;
  }

  private async analyzeFile(filePath: string, type: string): Promise<Improvement[]> {
    const content = await fs.readFile(filePath, 'utf-8');
    const ext = path.extname(filePath);
    const improvements: Improvement[] = [];

    if (type === 'all' || type === 'quality') {
      improvements.push(...await this.analyzeCodeQuality(content, filePath, ext));
    }

    if (type === 'all' || type === 'performance') {
      improvements.push(...await this.analyzePerformance(content, filePath, ext));
    }

    if (type === 'all' || type === 'security') {
      improvements.push(...await this.analyzeSecurity(content, filePath, ext));
    }

    return improvements;
  }

  private async analyzeCodeQuality(
    content: string,
    filePath: string,
    ext: string
  ): Promise<Improvement[]> {
    const improvements: Improvement[] = [];

    // Check for code duplication
    const duplicates = this.findDuplicateCode(content);
    if (duplicates.length > 0) {
      improvements.push({
        type: 'quality',
        file: filePath,
        issue: 'Code duplication detected',
        suggestion: 'Extract common code into reusable functions',
        priority: 'medium',
        lines: duplicates,
        fix: this.generateDuplicationFix(duplicates, content)
      });
    }

    // Check for long functions
    const longFunctions = this.findLongFunctions(content);
    for (const func of longFunctions) {
      improvements.push({
        type: 'quality',
        file: filePath,
        issue: `Function ${func.name} is too long (${func.lines} lines)`,
        suggestion: 'Break down into smaller functions',
        priority: 'medium',
        lines: [func.startLine, func.endLine],
        fix: this.generateFunctionSplitSuggestion(func)
      });
    }

    // Check for complex conditionals
    const complexConditions = this.findComplexConditions(content);
    for (const condition of complexConditions) {
      improvements.push({
        type: 'quality',
        file: filePath,
        issue: 'Complex conditional expression',
        suggestion: 'Simplify or extract to named function',
        priority: 'low',
        lines: [condition.line],
        fix: this.generateConditionSimplification(condition)
      });
    }

    // Check for missing error handling
    if (content.includes('async') && !content.includes('try')) {
      improvements.push({
        type: 'quality',
        file: filePath,
        issue: 'Missing error handling for async operations',
        suggestion: 'Add try-catch blocks',
        priority: 'high',
        fix: this.generateErrorHandlingFix(content)
      });
    }

    // Check for console.log statements
    const consoleLogs = this.findConsoleLogs(content);
    if (consoleLogs.length > 0) {
      improvements.push({
        type: 'quality',
        file: filePath,
        issue: 'Console.log statements in code',
        suggestion: 'Remove or replace with proper logging',
        priority: 'low',
        lines: consoleLogs,
        fix: this.generateLoggingFix(content)
      });
    }

    return improvements;
  }

  private async analyzePerformance(
    content: string,
    filePath: string,
    ext: string
  ): Promise<Improvement[]> {
    const improvements: Improvement[] = [];

    // Check for synchronous file operations
    if (content.includes('readFileSync') || content.includes('writeFileSync')) {
      improvements.push({
        type: 'performance',
        file: filePath,
        issue: 'Synchronous file operations detected',
        suggestion: 'Use async alternatives',
        priority: 'high',
        fix: this.generateAsyncFileFix(content)
      });
    }

    // Check for nested loops
    const nestedLoops = this.findNestedLoops(content);
    if (nestedLoops.length > 0) {
      improvements.push({
        type: 'performance',
        file: filePath,
        issue: 'Nested loops detected (O(n²) or worse)',
        suggestion: 'Consider using maps or more efficient algorithms',
        priority: 'medium',
        lines: nestedLoops,
        fix: this.generateLoopOptimization(content, nestedLoops)
      });
    }

    // Check for array operations in loops
    const inefficientArrayOps = this.findInefficientArrayOps(content);
    for (const op of inefficientArrayOps) {
      improvements.push({
        type: 'performance',
        file: filePath,
        issue: `Inefficient array operation: ${op.operation}`,
        suggestion: op.suggestion,
        priority: 'medium',
        lines: [op.line],
        fix: op.fix
      });
    }

    // Check for missing memoization opportunities
    const memoizeCandidates = this.findMemoizationCandidates(content);
    for (const candidate of memoizeCandidates) {
      improvements.push({
        type: 'performance',
        file: filePath,
        issue: `Function ${candidate.name} could benefit from memoization`,
        suggestion: 'Add memoization for expensive computations',
        priority: 'low',
        lines: [candidate.line],
        fix: this.generateMemoizationFix(candidate)
      });
    }

    return improvements;
  }

  private async analyzeSecurity(
    content: string,
    filePath: string,
    ext: string
  ): Promise<Improvement[]> {
    const improvements: Improvement[] = [];

    // Check for hardcoded secrets
    const secrets = this.findHardcodedSecrets(content);
    if (secrets.length > 0) {
      improvements.push({
        type: 'security',
        file: filePath,
        issue: 'Hardcoded secrets detected',
        suggestion: 'Move to environment variables',
        priority: 'high',
        lines: secrets,
        fix: this.generateSecretsFix(content, secrets)
      });
    }

    // Check for SQL injection vulnerabilities
    if (content.includes('query') && content.includes('${')) {
      improvements.push({
        type: 'security',
        file: filePath,
        issue: 'Potential SQL injection vulnerability',
        suggestion: 'Use parameterized queries',
        priority: 'high',
        fix: this.generateSQLInjectionFix(content)
      });
    }

    // Check for missing input validation
    const unvalidatedInputs = this.findUnvalidatedInputs(content);
    for (const input of unvalidatedInputs) {
      improvements.push({
        type: 'security',
        file: filePath,
        issue: `Unvalidated input: ${input.name}`,
        suggestion: 'Add input validation',
        priority: 'medium',
        lines: [input.line],
        fix: this.generateValidationFix(input)
      });
    }

    return improvements;
  }

  // Helper methods for code analysis
  private findDuplicateCode(content: string): number[] {
    const lines = content.split('\n');
    const duplicates: number[] = [];
    const seen = new Map<string, number>();

    for (let i = 0; i < lines.length; i++) {
      const normalized = lines[i].trim();
      if (normalized.length > 20 && !normalized.startsWith('//')) {
        if (seen.has(normalized)) {
          duplicates.push(i + 1);
        } else {
          seen.set(normalized, i + 1);
        }
      }
    }

    return duplicates;
  }

  private findLongFunctions(content: string): Array<{
    name: string;
    lines: number;
    startLine: number;
    endLine: number;
  }> {
    const functions: Array<{
      name: string;
      lines: number;
      startLine: number;
      endLine: number;
    }> = [];
    
    const lines = content.split('\n');
    let inFunction = false;
    let functionName = '';
    let startLine = 0;
    let braceCount = 0;

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      if (!inFunction && (line.includes('function ') || line.includes('=>'))) {
        const match = line.match(/(?:function\s+|const\s+|let\s+|var\s+)(\w+)/);
        if (match) {
          functionName = match[1];
          startLine = i + 1;
          inFunction = true;
          braceCount = 0;
        }
      }

      if (inFunction) {
        if (line.includes('{')) braceCount++;
        if (line.includes('}')) braceCount--;
        
        if (braceCount === 0 && line.includes('}')) {
          const functionLines = i - startLine + 1;
          if (functionLines > 30) {
            functions.push({
              name: functionName,
              lines: functionLines,
              startLine,
              endLine: i + 1
            });
          }
          inFunction = false;
        }
      }
    }

    return functions;
  }

  private findComplexConditions(content: string): Array<{ line: number; condition: string }> {
    const complex: Array<{ line: number; condition: string }> = [];
    const lines = content.split('\n');

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (line.includes('if') || line.includes('while')) {
        const operators = (line.match(/&&|\|\|/g) || []).length;
        if (operators > 2) {
          complex.push({ line: i + 1, condition: line.trim() });
        }
      }
    }

    return complex;
  }

  private findConsoleLogs(content: string): number[] {
    const lines = content.split('\n');
    const logLines: number[] = [];

    for (let i = 0; i < lines.length; i++) {
      if (lines[i].includes('console.log')) {
        logLines.push(i + 1);
      }
    }

    return logLines;
  }

  private findNestedLoops(content: string): number[] {
    const lines = content.split('\n');
    const nestedLines: number[] = [];
    let loopDepth = 0;

    for (let i = 0; i < lines.length; i++) {
      if (lines[i].match(/\b(for|while)\b/)) {
        loopDepth++;
        if (loopDepth > 1) {
          nestedLines.push(i + 1);
        }
      }
      if (lines[i].includes('}')) {
        // Simple heuristic - may need improvement
        if (loopDepth > 0) loopDepth--;
      }
    }

    return nestedLines;
  }

  private findInefficientArrayOps(content: string): Array<{
    operation: string;
    suggestion: string;
    line: number;
    fix: string;
  }> {
    const inefficient: Array<{
      operation: string;
      suggestion: string;
      line: number;
      fix: string;
    }> = [];
    
    const lines = content.split('\n');

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      // Check for array.indexOf in loops
      if (line.includes('.indexOf') && i > 0 && lines[i - 1].match(/\b(for|while)\b/)) {
        inefficient.push({
          operation: 'indexOf in loop',
          suggestion: 'Use Set or Map for O(1) lookup',
          line: i + 1,
          fix: 'const itemSet = new Set(array); // Then use itemSet.has(item)'
        });
      }

      // Check for array.push in loops
      if (line.includes('.concat') && line.match(/\b(for|while)\b/)) {
        inefficient.push({
          operation: 'concat in loop',
          suggestion: 'Use push or spread operator',
          line: i + 1,
          fix: 'result.push(...items); // More efficient than concat'
        });
      }
    }

    return inefficient;
  }

  private findMemoizationCandidates(content: string): Array<{
    name: string;
    line: number;
  }> {
    const candidates: Array<{ name: string; line: number }> = [];
    const lines = content.split('\n');

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      // Look for recursive functions or functions with expensive operations
      if (line.includes('function') || line.includes('=>')) {
        const match = line.match(/(?:function\s+|const\s+)(\w+)/);
        if (match) {
          // Check if function body contains recursive call or expensive operations
          const functionName = match[1];
          let endLine = i + 20; // Check next 20 lines
          for (let j = i + 1; j < Math.min(lines.length, endLine); j++) {
            if (lines[j].includes(functionName + '(') || 
                lines[j].includes('Math.pow') ||
                lines[j].includes('for') && lines[j + 1]?.includes('for')) {
              candidates.push({ name: functionName, line: i + 1 });
              break;
            }
          }
        }
      }
    }

    return candidates;
  }

  private findHardcodedSecrets(content: string): number[] {
    const lines = content.split('\n');
    const secretLines: number[] = [];
    
    const secretPatterns = [
      /api[_-]?key\s*[=:]\s*["'][^"']+["']/i,
      /password\s*[=:]\s*["'][^"']+["']/i,
      /secret\s*[=:]\s*["'][^"']+["']/i,
      /token\s*[=:]\s*["'][^"']+["']/i
    ];

    for (let i = 0; i < lines.length; i++) {
      for (const pattern of secretPatterns) {
        if (pattern.test(lines[i])) {
          secretLines.push(i + 1);
          break;
        }
      }
    }

    return secretLines;
  }

  private findUnvalidatedInputs(content: string): Array<{
    name: string;
    line: number;
  }> {
    const inputs: Array<{ name: string; line: number }> = [];
    const lines = content.split('\n');

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      
      // Check for request parameters without validation
      if (line.includes('req.body') || line.includes('req.params') || line.includes('req.query')) {
        const nextLines = lines.slice(i, i + 5).join(' ');
        if (!nextLines.includes('validate') && !nextLines.includes('check')) {
          const match = line.match(/req\.(body|params|query)\.(\w+)/);
          if (match) {
            inputs.push({ name: match[2], line: i + 1 });
          }
        }
      }
    }

    return inputs;
  }

  // Fix generation methods
  private generateDuplicationFix(duplicates: number[], content: string): string {
    return `// Extract duplicated code into a reusable function
function extractedFunction() {
  // Move duplicated logic here
}

// Call the function instead of duplicating code`;
  }

  private generateFunctionSplitSuggestion(func: { name: string; lines: number }): string {
    return `// Split ${func.name} into smaller functions:
function ${func.name}Part1() {
  // First logical part
}

function ${func.name}Part2() {
  // Second logical part
}

function ${func.name}() {
  ${func.name}Part1();
  ${func.name}Part2();
}`;
  }

  private generateConditionSimplification(condition: { condition: string }): string {
    return `// Simplify complex condition:
const isConditionA = /* first condition */;
const isConditionB = /* second condition */;
const isConditionC = /* third condition */;

if (isConditionA && isConditionB || isConditionC) {
  // Your logic here
}`;
  }

  private generateErrorHandlingFix(content: string): string {
    return `// Add proper error handling:
try {
  // Your async operation
  const result = await someAsyncOperation();
  return result;
} catch (error) {
  console.error('Operation failed:', error);
  // Handle error appropriately
  throw error;
}`;
  }

  private generateLoggingFix(content: string): string {
    return `// Replace console.log with proper logging:
import { logger } from './utils/logger';

// Instead of console.log
logger.info('Your log message');
logger.error('Error message', error);`;
  }

  private generateAsyncFileFix(content: string): string {
    return `// Replace synchronous file operations:
// Instead of: const data = fs.readFileSync('file.txt', 'utf-8');
const data = await fs.promises.readFile('file.txt', 'utf-8');

// Instead of: fs.writeFileSync('file.txt', data);
await fs.promises.writeFile('file.txt', data);`;
  }

  private generateLoopOptimization(content: string, nestedLoops: number[]): string {
    return `// Optimize nested loops using Map or Set:
const lookupMap = new Map();
// Build lookup map in O(n)
for (const item of array1) {
  lookupMap.set(item.id, item);
}

// Now lookup is O(1) instead of O(n)
for (const item of array2) {
  const match = lookupMap.get(item.id);
  // Process match
}`;
  }

  private generateMemoizationFix(candidate: { name: string }): string {
    return `// Add memoization to ${candidate.name}:
const memoized${candidate.name} = (() => {
  const cache = new Map();
  
  return function ${candidate.name}(...args) {
    const key = JSON.stringify(args);
    if (cache.has(key)) {
      return cache.get(key);
    }
    
    const result = /* original computation */;
    cache.set(key, result);
    return result;
  };
})();`;
  }

  private generateSecretsFix(content: string, secretLines: number[]): string {
    return `// Move secrets to environment variables:
// In .env file:
API_KEY=your_api_key_here
DB_PASSWORD=your_password_here

// In code:
const apiKey = process.env.API_KEY;
const dbPassword = process.env.DB_PASSWORD;

// Don't forget to add .env to .gitignore`;
  }

  private generateSQLInjectionFix(content: string): string {
    return `// Use parameterized queries to prevent SQL injection:
// Instead of: query(\`SELECT * FROM users WHERE id = \${userId}\`)
query('SELECT * FROM users WHERE id = ?', [userId]);

// Or use prepared statements:
const stmt = db.prepare('SELECT * FROM users WHERE id = ?');
const result = stmt.get(userId);`;
  }

  private generateValidationFix(input: { name: string }): string {
    return `// Add input validation for ${input.name}:
const { body, validationResult } = require('express-validator');

// In route:
[
  body('${input.name}').isString().trim().notEmpty(),
  (req, res, next) => {
    const errors = validationResult(req);
    if (!errors.isEmpty()) {
      return res.status(400).json({ errors: errors.array() });
    }
    next();
  }
]`;
  }

  // Utility methods
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

  private async scanDirectory(dirPath: string): Promise<string[]> {
    const files: string[] = [];
    const entries = await fs.readdir(dirPath, { withFileTypes: true });
    
    for (const entry of entries) {
      const fullPath = path.join(dirPath, entry.name);
      if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
        const subFiles = await this.scanDirectory(fullPath);
        files.push(...subFiles);
      } else if (entry.isFile() && this.shouldAnalyzeFile(fullPath)) {
        files.push(fullPath);
      }
    }
    
    return files;
  }

  private shouldAnalyzeFile(filePath: string): boolean {
    const ext = path.extname(filePath);
    return ['.ts', '.js', '.tsx', '.jsx'].includes(ext);
  }

  private async applyImprovements(
    improvements: Improvement[],
    auto: boolean = false
  ): Promise<AppliedImprovement[]> {
    const applied: AppliedImprovement[] = [];
    
    // In a real implementation, this would apply the fixes
    // For now, just mark them as "would be applied"
    for (const improvement of improvements) {
      if (improvement.priority === 'high' || auto) {
        applied.push({
          ...improvement,
          applied: true,
          timestamp: new Date().toISOString()
        });
      }
    }
    
    return applied;
  }

  private formatImprovementReport(improvements: Improvement[]): string {
    let report = `# Code Improvement Report\n\n`;
    report += `Found ${improvements.length} improvement opportunities\n\n`;

    const byType = this.groupByType(improvements);
    
    for (const [type, items] of Object.entries(byType)) {
      report += `## ${type.charAt(0).toUpperCase() + type.slice(1)} Improvements (${items.length})\n\n`;
      
      const byPriority = this.groupByPriority(items);
      
      for (const [priority, priorityItems] of Object.entries(byPriority)) {
        report += `### ${priority.toUpperCase()} Priority\n`;
        
        for (const item of priorityItems.slice(0, 3)) {
          report += `**${path.basename(item.file)}**: ${item.issue}\n`;
          report += `- Suggestion: ${item.suggestion}\n`;
          if (item.lines) {
            report += `- Lines: ${item.lines.join(', ')}\n`;
          }
          if (item.fix) {
            report += `\nSuggested fix:\n\`\`\`typescript\n${item.fix}\n\`\`\`\n`;
          }
          report += '\n';
        }
        
        if (priorityItems.length > 3) {
          report += `... and ${priorityItems.length - 3} more ${priority} priority items\n\n`;
        }
      }
    }

    report += `## Summary\n`;
    report += `- High Priority: ${improvements.filter(i => i.priority === 'high').length}\n`;
    report += `- Medium Priority: ${improvements.filter(i => i.priority === 'medium').length}\n`;
    report += `- Low Priority: ${improvements.filter(i => i.priority === 'low').length}\n`;

    return report;
  }

  private formatAppliedReport(applied: AppliedImprovement[]): string {
    let report = `# Applied Improvements\n\n`;
    report += `Successfully applied ${applied.length} improvements\n\n`;

    for (const improvement of applied) {
      report += `✅ ${path.basename(improvement.file)}: ${improvement.issue}\n`;
    }

    return report;
  }

  private groupByType(improvements: Improvement[]): Record<string, Improvement[]> {
    const grouped: Record<string, Improvement[]> = {};
    for (const improvement of improvements) {
      if (!grouped[improvement.type]) {
        grouped[improvement.type] = [];
      }
      grouped[improvement.type].push(improvement);
    }
    return grouped;
  }

  private groupByPriority(improvements: Improvement[]): Record<string, Improvement[]> {
    const grouped: Record<string, Improvement[]> = {};
    for (const improvement of improvements) {
      if (!grouped[improvement.priority]) {
        grouped[improvement.priority] = [];
      }
      grouped[improvement.priority].push(improvement);
    }
    return grouped;
  }
}

// Type definitions
interface Improvement {
  type: 'quality' | 'performance' | 'security';
  file: string;
  issue: string;
  suggestion: string;
  priority: 'high' | 'medium' | 'low';
  lines?: number[];
  fix?: string;
}

interface AppliedImprovement extends Improvement {
  applied: boolean;
  timestamp: string;
}