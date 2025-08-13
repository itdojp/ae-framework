import { describe, test, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import { SlashCommandManager } from '../../src/commands/slash-command-manager.js';
import { PhaseStateManager } from '../../src/utils/phase-state-manager.js';

describe('SlashCommandManager', () => {
  const testDir = path.join(process.cwd(), '.test-slash-commands');
  let manager: SlashCommandManager;

  beforeEach(async () => {
    // Create test directory
    await fs.promises.mkdir(testDir, { recursive: true });
    manager = new SlashCommandManager(testDir);
  });

  afterEach(async () => {
    // Clean up test directory
    await fs.promises.rm(testDir, { recursive: true, force: true });
  });

  describe('execute', () => {
    test('should execute help command', async () => {
      const result = await manager.execute('/help');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Available Commands');
      expect(result.message).toContain('PHASE COMMANDS');
      expect(result.message).toContain('WORKFLOW COMMANDS');
    });

    test('should show help for specific command', async () => {
      const result = await manager.execute('/help /intent');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Command: /intent');
      expect(result.message).toContain('Description:');
      expect(result.message).toContain('Usage:');
    });

    test('should handle unknown command', async () => {
      const result = await manager.execute('/unknown');
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('Unknown command');
    });

    test('should resolve command aliases', async () => {
      const result = await manager.execute('/h');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Available Commands');
    });
  });

  describe('project workflow commands', () => {
    test('should initialize project', async () => {
      const result = await manager.execute('/init Test Project');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Initialized project: Test Project');
      expect(result.data).toBeDefined();
      expect(result.nextCommand).toBe('/status');
    });

    test('should show status', async () => {
      await manager.execute('/init Test Project');
      const result = await manager.execute('/status');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Project Status Report');
      expect(result.data.currentPhase).toBe('intent');
    });

    test('should handle status without project', async () => {
      const result = await manager.execute('/status');
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('No project found');
      expect(result.nextCommand).toBe('/init');
    });

    test('should complete phase', async () => {
      await manager.execute('/init Test Project');
      
      // Start intent phase (initialize in base agent will handle this)
      const phaseManager = new PhaseStateManager(testDir);
      await phaseManager.startPhase('intent');
      
      const result = await manager.execute('/complete requirements.md');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Completed phase: intent');
      expect(result.nextCommand).toBe('/approve'); // Since approvals are required
    });

    test('should approve phase', async () => {
      await manager.execute('/init Test Project');
      
      const phaseManager = new PhaseStateManager(testDir);
      await phaseManager.startPhase('intent');
      await phaseManager.completePhase('intent', ['requirements.md']);
      
      const result = await manager.execute('/approve Good work');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Approved phase: intent');
      expect(result.nextCommand).toBe('/next');
    });

    test('should transition to next phase', async () => {
      await manager.execute('/init Test Project');
      
      const phaseManager = new PhaseStateManager(testDir);
      await phaseManager.startPhase('intent');
      await phaseManager.completePhase('intent', []);
      await phaseManager.approvePhase('intent', 'CLI');
      
      const result = await manager.execute('/next');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Transitioned to phase: formal');
      expect(result.data.nextPhase).toBe('formal');
    });

    test('should prevent transition without completion', async () => {
      await manager.execute('/init Test Project');
      
      const phaseManager = new PhaseStateManager(testDir);
      await phaseManager.startPhase('intent');
      
      const result = await manager.execute('/next');
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('must be completed first');
      expect(result.nextCommand).toBe('/complete');
    });
  });

  describe('phase commands', () => {
    test('should extract intent from requirements', async () => {
      await manager.execute('/init Test Project');
      
      const result = await manager.execute('/intent The system must authenticate users');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Extracted');
      expect(result.message).toContain('requirements');
      expect(result.data).toBeDefined();
    });

    test('should require phase for phase-specific commands', async () => {
      await manager.execute('/init Test Project');
      
      // Try to run formal command in intent phase
      const result = await manager.execute('/formal openapi');
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('requires phase formal');
      expect(result.message).toContain('current phase is intent');
    });
  });

  describe('utility commands', () => {
    test('should show context', async () => {
      await manager.execute('/init Test Project');
      
      const result = await manager.execute('/context');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Current Context');
      expect(result.message).toContain('Project: Test Project');
      expect(result.message).toContain('Current Phase: intent');
    });

    test('should show timeline', async () => {
      await manager.execute('/init Test Project');
      
      const result = await manager.execute('/timeline');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Phase Timeline');
      expect(result.data).toHaveLength(6); // 6 phases
    });

    test('should manage steering documents', async () => {
      const result = await manager.execute('/steering');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Available steering documents');
    });

    test('should load steering document', async () => {
      // Create a test steering document
      const steeringDir = path.join(testDir, '.ae', 'steering');
      await fs.promises.mkdir(steeringDir, { recursive: true });
      await fs.promises.writeFile(
        path.join(steeringDir, 'test.md'),
        '# Test Document'
      );
      
      const result = await manager.execute('/steering load test');
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Loaded test');
      expect(result.data).toContain('Test Document');
    });
  });

  describe('parseCommandFromText', () => {
    test('should extract commands from text', () => {
      const text = 'Please /init my project and then /status to check';
      const commands = manager.parseCommandFromText(text);
      
      expect(commands).toHaveLength(2);
      expect(commands[0]).toBe('/init my project and then');
      expect(commands[1]).toBe('/status to check');
    });

    test('should handle multiple commands', () => {
      const text = '/help /init /status';
      const commands = manager.parseCommandFromText(text);
      
      expect(commands).toHaveLength(3);
      expect(commands).toEqual(['/help', '/init', '/status']);
    });

    test('should return empty array for no commands', () => {
      const text = 'This text has no commands';
      const commands = manager.parseCommandFromText(text);
      
      expect(commands).toHaveLength(0);
    });
  });

  describe('executeSequence', () => {
    test('should execute commands in sequence', async () => {
      const commands = ['/init Test', '/status'];
      const results = await manager.executeSequence(commands);
      
      expect(results).toHaveLength(3); // init, status (from nextCommand), status
      expect(results[0].success).toBe(true);
      expect(results[0].message).toContain('Initialized');
      expect(results[1].success).toBe(true);
      expect(results[1].message).toContain('Project Status Report');
    });

    test('should stop on failure', async () => {
      const commands = ['/unknown', '/status'];
      const results = await manager.executeSequence(commands);
      
      expect(results).toHaveLength(1);
      expect(results[0].success).toBe(false);
    });

    test('should follow nextCommand suggestions', async () => {
      const commands = ['/init Test'];
      const results = await manager.executeSequence(commands);
      
      // Should execute /init and then /status (suggested)
      expect(results).toHaveLength(2);
      expect(results[0].nextCommand).toBe('/status');
      expect(results[1].message).toContain('Project Status Report');
    });
  });

  describe('command validation', () => {
    test('should validate command arguments', async () => {
      // Initialize project first to avoid phase check
      await manager.execute('/init Test');
      
      const result = await manager.execute('/intent');
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('Please provide requirement text');
    });

    test('should validate formal command arguments', async () => {
      await manager.execute('/init Test');
      
      // Move to formal phase
      const phaseManager = new PhaseStateManager(testDir);
      await phaseManager.startPhase('intent');
      await phaseManager.completePhase('intent', []);
      await phaseManager.approvePhase('intent', 'auto');
      await phaseManager.transitionToNextPhase();
      
      const result = await manager.execute('/formal');
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('Please specify specification type');
    });
  });

  describe('getCommands', () => {
    test('should return all registered commands', () => {
      const commands = manager.getCommands();
      
      expect(commands.length).toBeGreaterThan(10);
      
      const commandNames = commands.map(c => c.name);
      expect(commandNames).toContain('/intent');
      expect(commandNames).toContain('/formal');
      expect(commandNames).toContain('/test');
      expect(commandNames).toContain('/code');
      expect(commandNames).toContain('/verify');
      expect(commandNames).toContain('/operate');
      expect(commandNames).toContain('/help');
      expect(commandNames).toContain('/init');
      expect(commandNames).toContain('/status');
    });
  });
});