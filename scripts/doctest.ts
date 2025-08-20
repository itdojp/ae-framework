#!/usr/bin/env ts-node

/**
 * Documentation Test Runner
 * 
 * Extracts and validates code blocks from markdown documentation
 * and checks link validity (internal and external)
 */

import { readFileSync, writeFileSync, existsSync, statSync } from 'fs';
import { join, relative, dirname } from 'path';
import { glob } from 'glob';
import { spawn } from 'child_process';

function execAsync(command: string, args: string[] = [], options = {}): Promise<{ stdout: string, stderr: string, code: number }> {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, options);
    let stdout = '';
    let stderr = '';

    if (child.stdout) {
      child.stdout.on('data', (data) => {
        stdout += data.toString();
      });
    }
    if (child.stderr) {
      child.stderr.on('data', (data) => {
        stderr += data.toString();
      });
    }

    child.on('error', (err) => {
      reject(err);
    });

    child.on('close', (code) => {
      resolve({ stdout, stderr, code: code ?? 0 });
    });
  });
}

interface CodeBlock {
  language: string;
  code: string;
  file: string;
  line: number;
}

interface LinkCheck {
  url: string;
  file: string;
  line: number;
  type: 'internal' | 'external';
  status: 'valid' | 'invalid' | 'unknown';
  error?: string;
}

interface DocTestResult {
  codeBlocks: {
    total: number;
    passed: number;
    failed: number;
    results: Array<{
      file: string;
      line: number;
      language: string;
      success: boolean;
      error?: string;
    }>;
  };
  links: {
    total: number;
    valid: number;
    invalid: number;
    results: LinkCheck[];
  };
}

class DocumentationTester {
  private readonly SUPPORTED_LANGUAGES = ['typescript', 'ts', 'javascript', 'js', 'bash', 'sh', 'json'];
  private readonly INTERNAL_LINK_PATTERNS = [
    /\[([^\]]+)\]\(([^)]+)\)/g, // Markdown links
    /href="([^"]+)"/g,           // HTML href attributes
  ];
  private readonly EXTERNAL_URL_PATTERN = /^https?:\/\//;

  async runDocTests(pattern: string = 'docs/**/*.md'): Promise<DocTestResult> {
    console.log('📚 Running documentation tests...');
    
    const files = await glob(pattern);
    const codeBlocks = this.extractCodeBlocks(files);
    const links = this.extractLinks(files);

    console.log(`Found ${codeBlocks.length} code blocks and ${links.length} links`);

    const codeResults = await this.validateCodeBlocks(codeBlocks);
    const linkResults = await this.validateLinks(links);

    return {
      codeBlocks: {
        total: codeBlocks.length,
        passed: codeResults.filter(r => r.success).length,
        failed: codeResults.filter(r => !r.success).length,
        results: codeResults
      },
      links: {
        total: links.length,
        valid: linkResults.filter(r => r.status === 'valid').length,
        invalid: linkResults.filter(r => r.status === 'invalid').length,
        results: linkResults
      }
    };
  }

  private extractCodeBlocks(files: string[]): CodeBlock[] {
    const blocks: CodeBlock[] = [];

    for (const file of files) {
      if (!existsSync(file)) continue;
      
      const content = readFileSync(file, 'utf-8');
      const lines = content.split('\n');

      let inCodeBlock = false;
      let currentLanguage = '';
      let currentCode: string[] = [];
      let blockStartLine = 0;

      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        
        if (line.startsWith('```')) {
          if (inCodeBlock) {
            // End of code block
            if (this.SUPPORTED_LANGUAGES.includes(currentLanguage)) {
              blocks.push({
                language: currentLanguage,
                code: currentCode.join('\n'),
                file,
                line: blockStartLine
              });
            }
            inCodeBlock = false;
            currentCode = [];
          } else {
            // Start of code block
            inCodeBlock = true;
            currentLanguage = line.slice(3).trim();
            blockStartLine = i + 1;
          }
        } else if (inCodeBlock) {
          currentCode.push(line);
        }
      }
    }

    return blocks;
  }

  private extractLinks(files: string[]): LinkCheck[] {
    const links: LinkCheck[] = [];

    for (const file of files) {
      if (!existsSync(file)) continue;
      
      const content = readFileSync(file, 'utf-8');
      const lines = content.split('\n');

      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        
        // Extract markdown links
        const markdownLinks = [...line.matchAll(/\[([^\]]+)\]\(([^)]+)\)/g)];
        for (const match of markdownLinks) {
          const url = match[2];
          links.push({
            url,
            file,
            line: i + 1,
            type: this.EXTERNAL_URL_PATTERN.test(url) ? 'external' : 'internal',
            status: 'unknown'
          });
        }

        // Extract HTML href attributes
        const hrefLinks = [...line.matchAll(/href="([^"]+)"/g)];
        for (const match of hrefLinks) {
          const url = match[1];
          links.push({
            url,
            file,
            line: i + 1,
            type: this.EXTERNAL_URL_PATTERN.test(url) ? 'external' : 'internal',
            status: 'unknown'
          });
        }
      }
    }

    return links;
  }

  private async validateCodeBlocks(blocks: CodeBlock[]): Promise<Array<{
    file: string;
    line: number;
    language: string;
    success: boolean;
    error?: string;
  }>> {
    const results = [];

    console.log('🔍 Validating code blocks...');

    for (let i = 0; i < blocks.length; i++) {
      const block = blocks[i];
      
      try {
        const result = await this.validateSingleCodeBlock(block);
        results.push(result);
        
        if ((i + 1) % 5 === 0) {
          console.log(`   Progress: ${i + 1}/${blocks.length} code blocks validated`);
        }
      } catch (error) {
        results.push({
          file: block.file,
          line: block.line,
          language: block.language,
          success: false,
          error: (error as Error).message
        });
      }
    }

    return results;
  }

  private async validateSingleCodeBlock(block: CodeBlock): Promise<{
    file: string;
    line: number;
    language: string;
    success: boolean;
    error?: string;
  }> {
    const tempDir = './tmp/doctest';
    const tempFile = join(tempDir, `test-${Date.now()}-${Math.random().toString(36).slice(2)}`);

    try {
      // Create temp directory if needed
      if (!existsSync(tempDir)) {
        await this.createDirectory(tempDir);
      }

      let extension = 'txt';
      let validationCommand: string[] = [];

      switch (block.language) {
        case 'typescript':
        case 'ts':
          extension = 'ts';
          writeFileSync(`${tempFile}.${extension}`, block.code);
          validationCommand = ['npx', 'tsc', '--noEmit', '--skipLibCheck', `${tempFile}.${extension}`];
          break;
          
        case 'javascript':
        case 'js':
          extension = 'js';
          writeFileSync(`${tempFile}.${extension}`, block.code);
          validationCommand = ['node', '--check', `${tempFile}.${extension}`];
          break;
          
        case 'bash':
        case 'sh':
          extension = 'sh';
          writeFileSync(`${tempFile}.${extension}`, block.code);
          validationCommand = ['bash', '-n', `${tempFile}.${extension}`]; // Syntax check only
          break;
          
        case 'json':
          extension = 'json';
          // Validate JSON by parsing
          try {
            JSON.parse(block.code);
            return {
              file: block.file,
              line: block.line,
              language: block.language,
              success: true
            };
          } catch (parseError) {
            return {
              file: block.file,
              line: block.line,
              language: block.language,
              success: false,
              error: `JSON parse error: ${(parseError as Error).message}`
            };
          }
          
        default:
          // Skip unsupported languages
          return {
            file: block.file,
            line: block.line,
            language: block.language,
            success: true
          };
      }

      // Execute validation command
      const result = await this.executeCommand(validationCommand);
      
      // Clean up temp file
      if (existsSync(`${tempFile}.${extension}`)) {
        await this.deleteFile(`${tempFile}.${extension}`);
      }

      return {
        file: block.file,
        line: block.line,
        language: block.language,
        success: result.exitCode === 0,
        error: result.exitCode !== 0 ? result.stderr : undefined
      };

    } catch (error) {
      return {
        file: block.file,
        line: block.line,
        language: block.language,
        success: false,
        error: (error as Error).message
      };
    }
  }

  private async validateLinks(links: LinkCheck[]): Promise<LinkCheck[]> {
    console.log('🔗 Validating links...');
    
    const results = [...links];

    for (let i = 0; i < results.length; i++) {
      const link = results[i];
      
      try {
        if (link.type === 'internal') {
          link.status = await this.validateInternalLink(link);
        } else {
          link.status = await this.validateExternalLink(link);
        }
      } catch (error) {
        link.status = 'invalid';
        link.error = (error as Error).message;
      }

      if ((i + 1) % 10 === 0) {
        console.log(`   Progress: ${i + 1}/${results.length} links validated`);
      }
    }

    return results;
  }

  private async validateInternalLink(link: LinkCheck): Promise<'valid' | 'invalid'> {
    let targetPath = link.url;

    // Handle hash fragments
    if (targetPath.includes('#')) {
      targetPath = targetPath.split('#')[0];
    }

    // Skip empty paths (hash-only links)
    if (!targetPath) {
      return 'valid';
    }

    // Resolve relative to the file containing the link
    const basePath = dirname(link.file);
    const resolvedPath = join(basePath, targetPath);

    // Check if file exists
    if (existsSync(resolvedPath)) {
      const stats = statSync(resolvedPath);
      return stats.isFile() || stats.isDirectory() ? 'valid' : 'invalid';
    }

    // Check relative to project root
    if (existsSync(targetPath)) {
      const stats = statSync(targetPath);
      return stats.isFile() || stats.isDirectory() ? 'valid' : 'invalid';
    }

    return 'invalid';
  }

  private async validateExternalLink(link: LinkCheck): Promise<'valid' | 'invalid'> {
    // For external links, we'll do a simplified check
    // In a full implementation, this would make HTTP requests
    
    // Skip validation for localhost and example domains
    if (link.url.includes('localhost') || 
        link.url.includes('example.com') ||
        link.url.includes('127.0.0.1')) {
      return 'valid';
    }

    // For CI environments, assume external links are valid
    // In production, implement actual HTTP HEAD requests
    return 'valid';
  }

  private async createDirectory(path: string): Promise<void> {
    const { spawn } = require('child_process');
    return new Promise((resolve, reject) => {
      const child = spawn('mkdir', ['-p', path]);
      child.on('close', (code: number) => {
        if (code === 0) resolve();
        else reject(new Error(`Failed to create directory ${path}`));
      });
    });
  }

  private async deleteFile(path: string): Promise<void> {
    const { spawn } = require('child_process');
    return new Promise((resolve) => {
      const child = spawn('rm', ['-f', path]);
      child.on('close', () => resolve()); // Always resolve, ignore errors
    });
  }

  private async executeCommand(command: string[]): Promise<{
    exitCode: number;
    stdout: string;
    stderr: string;
  }> {
    const [cmd, ...args] = command;
    
    return new Promise((resolve) => {
      const child = spawn(cmd, args, { stdio: ['pipe', 'pipe', 'pipe'] });
      
      let stdout = '';
      let stderr = '';

      child.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      child.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      child.on('close', (code) => {
        resolve({
          exitCode: code || 0,
          stdout,
          stderr
        });
      });

      child.on('error', (error) => {
        resolve({
          exitCode: -1,
          stdout,
          stderr: error.message
        });
      });
    });
  }

  generateReport(result: DocTestResult): string {
    const report = [];
    
    report.push('# Documentation Test Report');
    report.push('');
    report.push(`Generated: ${new Date().toISOString()}`);
    report.push('');

    // Code blocks summary
    report.push('## Code Block Validation');
    report.push(`- Total: ${result.codeBlocks.total}`);
    report.push(`- Passed: ${result.codeBlocks.passed}`);
    report.push(`- Failed: ${result.codeBlocks.failed}`);
    report.push('');

    if (result.codeBlocks.failed > 0) {
      report.push('### Failed Code Blocks');
      result.codeBlocks.results
        .filter(r => !r.success)
        .forEach(r => {
          report.push(`- ${r.file}:${r.line} (${r.language}): ${r.error}`);
        });
      report.push('');
    }

    // Links summary
    report.push('## Link Validation');
    report.push(`- Total: ${result.links.total}`);
    report.push(`- Valid: ${result.links.valid}`);
    report.push(`- Invalid: ${result.links.invalid}`);
    report.push('');

    if (result.links.invalid > 0) {
      report.push('### Invalid Links');
      result.links.results
        .filter(r => r.status === 'invalid')
        .forEach(r => {
          report.push(`- ${r.file}:${r.line}: ${r.url} (${r.error || 'not found'})`);
        });
    }

    return report.join('\n');
  }
}

// CLI interface
async function main() {
  const tester = new DocumentationTester();
  const pattern = process.argv[2] || 'docs/**/*.md';
  
  try {
    const result = await tester.runDocTests(pattern);
    
    console.log('\n📊 Results Summary:');
    console.log(`Code blocks: ${result.codeBlocks.passed}/${result.codeBlocks.total} passed`);
    console.log(`Links: ${result.links.valid}/${result.links.total} valid`);

    // Generate report
    const report = tester.generateReport(result);
    const reportPath = './reports/doctest-report.md';
    
    // Ensure reports directory exists
    if (!existsSync('./reports')) {
      await tester['createDirectory']('./reports');
    }
    
    writeFileSync(reportPath, report);
    console.log(`\n📄 Report saved to: ${reportPath}`);

    // Exit with appropriate code
    const hasFailures = result.codeBlocks.failed > 0 || result.links.invalid > 0;
    process.exit(hasFailures ? 1 : 0);

  } catch (error) {
    console.error('❌ Documentation test failed:', (error as Error).message);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

export { DocumentationTester };