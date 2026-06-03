import path from 'node:path';
import { describe, test, expect, beforeEach, vi } from 'vitest';
import { SlashCommandManager } from '../../src/commands/slash-command-manager.js';
import * as fs from 'fs/promises';

// Mock file system
vi.mock('fs/promises');

describe('Extended Commands', () => {
  let manager: SlashCommandManager;
  const testProjectRoot = '/test/project';

  beforeEach(() => {
    vi.clearAllMocks();
    manager = new SlashCommandManager(testProjectRoot);
  });

  describe('/ae:analyze command', () => {
    test('should be registered with aliases', () => {
      const commands = manager.getCommands();
      const analyzeCommand = commands.find(cmd => cmd.name === '/ae:analyze');
      
      expect(analyzeCommand).toBeDefined();
      expect(analyzeCommand?.description).toContain('Deep code analysis');
      expect(analyzeCommand?.aliases).toContain('/analyze');
    });


    test.each([
      ['/ae:analyze /etc/passwd', 'analysis target path'],
      ['/ae:analyze ../outside.ts', 'analysis target path'],
      ['/ae:analyze src/../outside.ts', 'analysis target path'],
    ])('rejects unsafe analysis target %s before filesystem access', async (command, label) => {
      const result = await manager.execute(command);

      expect(result.success).toBe(false);
      expect(result.message).toContain(label);
      expect(fs.stat).not.toHaveBeenCalled();
      expect(fs.readFile).not.toHaveBeenCalled();
      expect(fs.readdir).not.toHaveBeenCalled();
    });

    test('should analyze a file', async () => {
      const testContent = `
        function longFunction() {
          // This is a very long function
          ${Array(60).fill('console.log("line");').join('\n')}
        }
        
        console.log("debug");
      `;

      vi.mocked(fs.stat).mockResolvedValue({ isDirectory: () => false } as any);
      vi.mocked(fs.readFile).mockResolvedValue(testContent);

      const result = await manager.execute('/ae:analyze test.ts');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Analyzed');
      expect(result.data).toBeDefined();
    });
  });

  describe('/ae:troubleshoot command', () => {
    test('should be registered with aliases', () => {
      const commands = manager.getCommands();
      const troubleshootCommand = commands.find(cmd => cmd.name === '/ae:troubleshoot');
      
      expect(troubleshootCommand).toBeDefined();
      expect(troubleshootCommand?.aliases).toContain('/troubleshoot');
      expect(troubleshootCommand?.aliases).toContain('/a:troubleshoot');
    });


    test.each([
      ['/ae:troubleshoot --logs=/etc/passwd', 'troubleshoot log path'],
      ['/ae:troubleshoot --logs=../outside.log', 'troubleshoot log path'],
      ['/ae:troubleshoot --logs=logs/../outside.log', 'troubleshoot log path'],
    ])('rejects unsafe troubleshoot log path %s before filesystem access', async (command, label) => {
      const result = await manager.execute(command);

      expect(result.success).toBe(false);
      expect(result.message).toContain(label);
      expect(fs.readFile).not.toHaveBeenCalled();
    });

    test('reads troubleshoot logs only under the approved project root', async () => {
      vi.mocked(fs.readFile).mockResolvedValue('ERROR failed to connect\ninfo recovered');

      const result = await manager.execute('/ae:troubleshoot log analysis --logs=logs/app.log');

      expect(result.success).toBe(true);
      expect(fs.readFile).toHaveBeenCalledWith(path.join(testProjectRoot, 'logs', 'app.log'), 'utf-8');
      expect(result.data?.detectedIssues?.[0]?.location?.file).toBe('logs/app.log');
    });

    test('should analyze described issue', async () => {
      const result = await manager.execute('/ae:troubleshoot Cannot find module express');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Found');
      expect(result.data).toBeDefined();
      expect(result.data.detectedIssues).toBeDefined();
      expect(Array.isArray(result.data.detectedIssues)).toBe(true);
    });

    test('should categorize issues correctly', async () => {
      const result = await manager.execute('/ae:troubleshoot --error="Cannot find module express"');
      
      expect(result.success).toBe(true);
      expect(result.data?.detectedIssues?.length).toBeGreaterThan(0);
    });
  });

  describe('/ae:improve command', () => {
    test('should be registered with aliases', () => {
      const commands = manager.getCommands();
      const improveCommand = commands.find(cmd => cmd.name === '/ae:improve');
      
      expect(improveCommand).toBeDefined();
      expect(improveCommand?.aliases).toContain('/improve');
      expect(improveCommand?.aliases).toContain('/a:improve');
    });


    test.each([
      ['/ae:improve /etc/passwd', 'improvement target path'],
      ['/ae:improve ../outside.ts', 'improvement target path'],
      ['/ae:improve src/../outside.ts', 'improvement target path'],
    ])('rejects unsafe improvement target %s before filesystem access', async (command, label) => {
      const result = await manager.execute(command);

      expect(result.success).toBe(false);
      expect(result.message).toContain(label);
      expect(fs.stat).not.toHaveBeenCalled();
      expect(fs.readFile).not.toHaveBeenCalled();
      expect(fs.writeFile).not.toHaveBeenCalled();
      expect(fs.readdir).not.toHaveBeenCalled();
    });

    test('should suggest improvements for code', async () => {
      const testContent = `
        const apiKey = "hardcoded-key-123";
        
        function getData(userId) {
          const result = readFileSync('data.json');
          return result;
        }
        
        for (let i = 0; i < items.length; i++) {
          for (let j = 0; j < items.length; j++) {
            // nested loop
          }
        }
      `;

      vi.mocked(fs.stat).mockResolvedValue({ isDirectory: () => false } as any);
      vi.mocked(fs.readFile).mockResolvedValue(testContent);

      const result = await manager.execute('/ae:improve test.js');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Found');
      expect(result.data).toBeDefined();
      expect(result.data?.improvements?.length).toBeGreaterThan(0);
    });
  });

  describe('/ae:document command', () => {
    test('should be registered with aliases', () => {
      const commands = manager.getCommands();
      const documentCommand = commands.find(cmd => cmd.name === '/ae:document');
      
      expect(documentCommand).toBeDefined();
      expect(documentCommand?.aliases).toContain('/document');
      expect(documentCommand?.aliases).toContain('/a:document');
    });


    test.each([
      ['/ae:document /etc/passwd', 'documentation target path'],
      ['/ae:document ../outside.ts', 'documentation target path'],
      ['/ae:document src/../outside.ts', 'documentation target path'],
    ])('rejects unsafe documentation target %s before filesystem access', async (command, label) => {
      const result = await manager.execute(command);

      expect(result.success).toBe(false);
      expect(result.message).toContain(label);
      expect(fs.stat).not.toHaveBeenCalled();
      expect(fs.readFile).not.toHaveBeenCalled();
      expect(fs.writeFile).not.toHaveBeenCalled();
      expect(fs.readdir).not.toHaveBeenCalled();
    });

    test('rejects unsafe documentation output directory before write', async () => {
      vi.mocked(fs.stat).mockResolvedValue({ isDirectory: () => false } as any);
      vi.mocked(fs.readFile).mockResolvedValue('export function test() {}');

      const result = await manager.execute('/ae:document src/test.ts --output=../outside-docs');

      expect(result.success).toBe(false);
      expect(result.message).toContain('documentation output directory');
      expect(fs.readFile).not.toHaveBeenCalled();
      expect(fs.readdir).not.toHaveBeenCalled();
      expect(fs.writeFile).not.toHaveBeenCalled();
    });

    test('writes documentation only under the approved project root', async () => {
      vi.mocked(fs.stat).mockResolvedValue({ isDirectory: () => false } as any);
      vi.mocked(fs.readFile).mockResolvedValue('export function test() {}');
      vi.mocked(fs.writeFile).mockResolvedValue(undefined as any);

      const result = await manager.execute('/ae:document src/test.ts --output=docs/generated');

      expect(result.success).toBe(true);
      expect(fs.writeFile).toHaveBeenCalledTimes(1);
      expect(vi.mocked(fs.writeFile).mock.calls[0]?.[0]).toBe(path.join(testProjectRoot, 'docs', 'generated', 'test.md'));
    });

    test.skip('should generate documentation for TypeScript file', async () => {
      const testContent = `
        /**
         * User class for managing users
         */
        export class User {
          private id: string;
          public name: string;
          
          constructor(id: string, name: string) {
            this.id = id;
            this.name = name;
          }
          
          /**
           * Get user display name
           */
          public getDisplayName(): string {
            return this.name;
          }
        }
        
        /**
         * Create a new user
         */
        export function createUser(name: string): User {
          return new User(Date.now().toString(), name);
        }
      `;

      vi.mocked(fs.stat).mockResolvedValue({ isDirectory: () => false } as any);
      vi.mocked(fs.readFile).mockResolvedValue(testContent);

      const result = await manager.execute('/ae:document user.ts');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Generated documentation');
    });

    test.skip('should support different documentation formats', async () => {
      const testContent = 'export function test() {}';
      
      vi.mocked(fs.stat).mockResolvedValue({ isDirectory: () => false } as any);
      vi.mocked(fs.readFile).mockResolvedValue(testContent);

      // Test JSDoc format
      const jsdocResult = await manager.execute('/ae:document test.js --format=jsdoc');
      expect(jsdocResult.success).toBe(true);
      expect(jsdocResult.message).toContain('Generated documentation');
      
      // Test API format
      const apiResult = await manager.execute('/ae:document test.js --format=api-json');
      expect(apiResult.success).toBe(true);
      expect(apiResult.message).toContain('Generated documentation');
    });
  });

  describe('Command integration', () => {
    test('should list all extended commands', () => {
      const commands = manager.getCommands();
      const extendedCommands = commands.filter(cmd => 
        cmd.name.startsWith('/ae:')
      );
      
      expect(extendedCommands.length).toBe(7);
      expect(extendedCommands.map(c => c.name)).toContain('/ae:analyze');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:troubleshoot');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:improve');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:document');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:persona');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:installer');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:mcp');
    });

    test.skip('should work with command aliases', async () => {
      const testContent = 'function test() {}';
      
      vi.mocked(fs.stat).mockResolvedValue({ isDirectory: () => false } as any);
      vi.mocked(fs.readFile).mockResolvedValue(testContent);

      // Test analyze alias
      const analyzeResult = await manager.execute('/analyze test.ts');
      expect(analyzeResult.success).toBe(true);
      
      // Test troubleshoot alias
      const troubleshootResult = await manager.execute('/troubleshoot --error="Cannot find module"');
      expect(troubleshootResult.success).toBe(true);
      
      // Test improve alias
      const improveResult = await manager.execute('/improve test.ts');
      expect(improveResult.success).toBe(true);
      
      // Test document alias
      const documentResult = await manager.execute('/document test.ts');
      expect(documentResult.success).toBe(true);
    });
  });
});
