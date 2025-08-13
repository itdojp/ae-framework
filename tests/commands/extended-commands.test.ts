import { describe, test, expect, beforeEach, vi } from 'vitest';
import { SlashCommandManager } from '../../src/commands/slash-command-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';

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
      
      expect(extendedCommands.length).toBe(6);
      expect(extendedCommands.map(c => c.name)).toContain('/ae:analyze');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:troubleshoot');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:improve');
      expect(extendedCommands.map(c => c.name)).toContain('/ae:document');
      // expect(extendedCommands.map(c => c.name)).toContain('/ae:persona');  // Temporarily removed
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