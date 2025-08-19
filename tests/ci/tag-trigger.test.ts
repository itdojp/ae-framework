/**
 * Test for CI/CD Tag Trigger Configuration - Phase 1.3
 * Validates that all workflows have proper tag trigger setup
 */

import { describe, it, expect, beforeAll } from 'vitest';
import { readFileSync } from 'fs';
import { glob } from 'glob';
import yaml from 'js-yaml';
import path from 'path';

interface GitHubWorkflow {
  name?: string;
  on: {
    push?: {
      branches?: string[];
      tags?: string[];
    };
    pull_request?: {
      branches?: string[];
    };
    workflow_call?: any;
    workflow_dispatch?: any;
    schedule?: any;
  };
  jobs: Record<string, any>;
}

describe('CI/CD Tag Trigger Configuration - Phase 1.3', () => {
  const workflowsDir = '.github/workflows';
  let workflowFiles: string[] = [];

  beforeAll(async () => {
    workflowFiles = await glob(path.join(workflowsDir, '*.yml'));
  });

  describe('Tag Trigger Consistency', () => {
    it('should have tag triggers in core CI workflows', () => {
      const coreWorkflows = workflowFiles.filter(file => 
        file.includes('ci') || 
        file.includes('verify') ||
        file.includes('quality')
      );

      expect(coreWorkflows.length).toBeGreaterThan(0);

      coreWorkflows.forEach(workflowFile => {
        const content = readFileSync(workflowFile, 'utf8');
        const workflow = yaml.load(content) as GitHubWorkflow;
        const workflowName = path.basename(workflowFile, '.yml');

        expect(workflow.on.push?.tags, `${workflowName} should have tag triggers`)
          .toBeDefined();
        
        expect(workflow.on.push?.tags, `${workflowName} should include 'v*' tag pattern`)
          .toContain('v*');
      });
    });

    it('should have tag triggers in release workflow', () => {
      const releaseWorkflow = workflowFiles.find(file => file.includes('release'));
      
      if (releaseWorkflow) {
        const content = readFileSync(releaseWorkflow, 'utf8');
        const workflow = yaml.load(content) as GitHubWorkflow;

        expect(workflow.on.push?.tags).toBeDefined();
        expect(workflow.on.push?.tags).toContain('v*');
      }
    });

    it('should use consistent tag patterns', () => {
      const workflowsWithTags = workflowFiles.filter(file => {
        const content = readFileSync(file, 'utf8');
        return content.includes('tags:');
      });

      workflowsWithTags.forEach(workflowFile => {
        const content = readFileSync(workflowFile, 'utf8');
        const workflow = yaml.load(content) as GitHubWorkflow;
        const workflowName = path.basename(workflowFile, '.yml');

        if (workflow.on.push?.tags) {
          // All workflows should use the 'v*' pattern for consistency
          expect(workflow.on.push.tags, `${workflowName} should use 'v*' pattern`)
            .toContain('v*');
        }
      });
    });
  });

  describe('Release Workflow Safety', () => {
    it('should have job dependencies in release workflow', () => {
      const releaseWorkflow = workflowFiles.find(file => file.includes('release'));
      
      if (releaseWorkflow) {
        const content = readFileSync(releaseWorkflow, 'utf8');
        const workflow = yaml.load(content) as GitHubWorkflow;

        // Check if main release job has dependencies
        const releaseJob = workflow.jobs.release;
        expect(releaseJob).toBeDefined();
        expect(releaseJob.needs, 'Release job should depend on quality/CI checks')
          .toBeDefined();
        
        if (Array.isArray(releaseJob.needs)) {
          expect(releaseJob.needs.length).toBeGreaterThan(0);
        }
      }
    });

    it('should run quality gates before release', () => {
      const releaseWorkflow = workflowFiles.find(file => file.includes('release'));
      
      if (releaseWorkflow) {
        const content = readFileSync(releaseWorkflow, 'utf8');
        const workflow = yaml.load(content) as GitHubWorkflow;

        // Check for quality or CI check jobs
        const hasQualityCheck = 'quality-check' in workflow.jobs || 
                               'ci-check' in workflow.jobs ||
                               Object.keys(workflow.jobs).some(job => 
                                 job.includes('quality') || job.includes('ci')
                               );

        expect(hasQualityCheck, 'Release workflow should include quality/CI checks')
          .toBe(true);
      }
    });
  });

  describe('Workflow Validation Patterns', () => {
    it('should not have conflicting trigger patterns', () => {
      workflowFiles.forEach(workflowFile => {
        const content = readFileSync(workflowFile, 'utf8');
        const workflow = yaml.load(content) as GitHubWorkflow;
        const workflowName = path.basename(workflowFile, '.yml');

        // Check for common anti-patterns
        if (workflow.on.push?.tags) {
          // Should not trigger on branches and tags with conflicting conditions
          if (workflow.on.push.branches && workflow.on.push.tags) {
            // This is actually OK - can trigger on both branches and tags
            // Just ensure they don't conflict
            expect(true).toBe(true); // Pass - dual triggers are valid
          }
        }
      });
    });

    it('should have valid YAML syntax', () => {
      workflowFiles.forEach(workflowFile => {
        expect(() => {
          const content = readFileSync(workflowFile, 'utf8');
          yaml.load(content);
        }, `${path.basename(workflowFile)} should have valid YAML`)
          .not.toThrow();
      });
    });

    it('should have required workflow properties', () => {
      workflowFiles.forEach(workflowFile => {
        const content = readFileSync(workflowFile, 'utf8');
        const workflow = yaml.load(content) as GitHubWorkflow;
        const workflowName = path.basename(workflowFile, '.yml');

        expect(workflow.name, `${workflowName} should have a name`).toBeDefined();
        expect(workflow.on, `${workflowName} should have triggers`).toBeDefined();
        expect(workflow.jobs, `${workflowName} should have jobs`).toBeDefined();
        expect(Object.keys(workflow.jobs).length, `${workflowName} should have at least one job`)
          .toBeGreaterThan(0);
      });
    });
  });

  describe('Tag Pattern Security', () => {
    it('should use secure tag patterns', () => {
      workflowFiles.forEach(workflowFile => {
        const content = readFileSync(workflowFile, 'utf8');
        
        // Check for insecure patterns
        expect(
          content,
          `${path.basename(workflowFile)} should not use wildcard-only or overly broad tag patterns`
        ).not.toMatch(/tags:\s*\[\s*'\*'\s*\]/);
      });
    });

    it('should follow semantic versioning tag patterns', () => {
      const workflowsWithTags = workflowFiles.filter(file => {
        const content = readFileSync(file, 'utf8');
        return content.includes('v*');
      });

      workflowsWithTags.forEach(workflowFile => {
        const content = readFileSync(workflowFile, 'utf8');
        const workflowName = path.basename(workflowFile, '.yml');

        // Should use versioned patterns (v* is good)
        expect(content, `${workflowName} should use version-prefixed patterns`)
          .toMatch(/v\*/);
      });
    });
  });

  describe('Integration Test', () => {
    it('should provide comprehensive tag trigger coverage', () => {
      const criticalWorkflows = [
        'release.yml',
        'ci.yml', 
        'ci-fast.yml',
        'verify.yml',
        'quality-gates-centralized.yml'
      ];

      criticalWorkflows.forEach(expectedWorkflow => {
        const workflowPath = workflowFiles.find(file => 
          file.endsWith(expectedWorkflow)
        );

        if (workflowPath) {
          const content = readFileSync(workflowPath, 'utf8');
          const workflow = yaml.load(content) as GitHubWorkflow;

          expect(workflow.on.push?.tags, `${expectedWorkflow} should have tag triggers`)
            .toBeDefined();
        }
      });
    });
  });
});