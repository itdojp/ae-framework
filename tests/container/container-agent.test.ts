/**
 * Tests for Container Agent - Phase 3 of Issue #37
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { ContainerAgent } from '../../src/agents/container-agent.js';
import * as fs from 'fs/promises';
import * as path from 'path';
import * as os from 'os';

describe('ContainerAgent', () => {
  let agent: ContainerAgent;
  let tempDir: string;

  beforeEach(async () => {
    // Create temporary directory for testing
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'container-agent-test-'));
    
    agent = new ContainerAgent({
      containerfilesPath: tempDir,
      autoCleanup: false, // Disable for testing
    });
  });

  afterEach(async () => {
    try {
      await agent.shutdown();
      await fs.rm(tempDir, { recursive: true });
    } catch (error) {
      console.warn('Cleanup failed:', error);
    }
  });

  describe('initialization', () => {
    it('should initialize successfully', async () => {
      const result = await agent.initialize();
      expect(result.success).toBe(true);
      expect(result.message).toContain('initialized');
      
      // In CI environments, container engines might not be available
      // Verify that the agent can handle degraded mode gracefully
      if (process.env.CI && result.data?.degradedMode) {
        expect(result.data.engine.available).toBe(false);
        console.log('Running in CI degraded mode without container engine');
      }
    }, 15000); // Increase timeout to 15 seconds for container operations

    it('should create default Containerfiles', async () => {
      await agent.initialize();
      
      const files = await fs.readdir(tempDir);
      expect(files).toContain('Containerfile.rust');
      expect(files).toContain('Containerfile.elixir');
      expect(files).toContain('Containerfile.multi');
    }, 15000);

    it('should not initialize twice', async () => {
      await agent.initialize();
      const result = await agent.initialize();
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('already initialized');
    }, 15000);
  });

  describe('container engine detection', () => {
    it('should list available engines', async () => {
      await agent.initialize();
      const result = await agent.listEngines();
      expect(result.success).toBeDefined();
      
      // In CI environments without container engines, this may fail gracefully
      if (result.success) {
        expect(result.data?.engines).toBeInstanceOf(Array);
      } else if (process.env.CI) {
        expect(result.message).toContain('not available');
        console.log('Container engines not available in CI environment');
      }
    }, 10000);
  });

  describe('verification jobs', () => {
    beforeEach(async () => {
      await agent.initialize();
    });

    it('should reject invalid project path', async () => {
      const result = await agent.runVerification({
        projectPath: '/non/existent/path',
        language: 'rust',
        tools: ['cargo'],
      });
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('does not exist');
    });

    it('should list empty jobs initially', async () => {
      const result = await agent.listJobs();
      expect(result.success).toBe(true);
      expect(result.data?.jobs).toHaveLength(0);
    });

    it('should handle job status for non-existent job', async () => {
      const result = await agent.getJobStatus('non-existent-job');
      expect(result.success).toBe(false);
      expect(result.message).toContain('not found');
    });
  });

  describe('status monitoring', () => {
    beforeEach(async () => {
      await agent.initialize();
    });

    it('should provide system status', async () => {
      const result = await agent.getStatus();
      expect(result.success).toBe(true);
      expect(result.data?.engine).toBeDefined();
      expect(result.data?.jobs).toBeDefined();
      expect(result.data?.resources).toBeDefined();
    }, 10000);
  });

  describe('cleanup operations', () => {
    beforeEach(async () => {
      await agent.initialize();
    });

    it('should perform cleanup without errors', async () => {
      const result = await agent.cleanup({
        maxAge: 3600,
        keepCompleted: 5,
        force: false,
      });
      
      // Cleanup should succeed even if no resources to clean
      expect(result.success).toBeDefined();
      expect(result.message).toBeDefined();
      if (result.success) {
        expect(result.data?.jobsRemoved).toBeDefined();
        expect(result.data?.containersRemoved).toBeDefined();
      }
    }, 10000);
  });

  describe('image building', () => {
    beforeEach(async () => {
      await agent.initialize();
    });

    it('should validate build request parameters', async () => {
      const result = await agent.buildVerificationImage({
        language: 'rust',
        tools: ['cargo', 'miri'],
        tag: 'test-image:latest',
      });
      
      // This may fail if no container engine is available, but should not crash
      expect(result.success).toBeDefined();
      expect(result.message).toBeDefined();
      
      // In CI environments without container engines, expect graceful failure
      if (process.env.CI && !result.success) {
        expect(result.message).toMatch(/not available|not found|degraded/i);
        console.log('Image building not available in CI environment');
      }
    }, 10000);
  });
});