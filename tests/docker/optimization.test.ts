/**
 * Test for Docker Production Optimization - Phase 1.4  
 * Validates Docker security, performance, and size optimizations
 */

import { describe, it, expect } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import { readFileSync, existsSync } from 'fs';
import { exec } from 'child_process';
import { promisify } from 'util';

const execAsync = promisify(exec);

describe('Docker Production Optimization - Phase 1.4', () => {
  const dockerfile = 'podman/Dockerfile';
  const dockerignore = '.dockerignore';
  const dockerCompose = 'podman/compose.dev.yaml';
  const dockerComposeProd = 'podman/compose.prod.yaml';

  describe('Dockerfile Security and Optimization', () => {
    it(
      formatGWT('Dockerfile present', 'use multi-stage build', 'deps/build/runtime stages exist'),
      () => {
      expect(existsSync(dockerfile)).toBe(true);
      
      const content = readFileSync(dockerfile, 'utf8');
      
      // Should have multiple FROM statements for multi-stage
      const fromStatements = content.match(/^FROM /gm);
      expect(fromStatements?.length, 'Should have multi-stage builds').toBeGreaterThanOrEqual(3);
      
      // Should have named stages
      expect(content).toMatch(/FROM .* AS deps/);
      expect(content).toMatch(/FROM .* AS build/);
      expect(content).toMatch(/FROM .* AS runtime/);
    });

    it(
      formatGWT('Dockerfile production', 'prune dev dependencies', 'uses pnpm prune --prod'),
      () => {
      const content = readFileSync(dockerfile, 'utf8');
      
      // Should use pnpm prune --prod to remove dev dependencies
      expect(content, 'Should prune dev dependencies').toMatch(/pnpm prune --prod/);
    });

    it(
      formatGWT('Dockerfile security', 'use non-root user and chown', 'USER directive and --chown are present'),
      () => {
      const content = readFileSync(dockerfile, 'utf8');
      
      // Should create non-root user
      expect(content, 'Should create non-root user').toMatch(/adduser|addgroup/);
      
      // Should switch to non-root user
      expect(content, 'Should use USER directive').toMatch(/USER \w+/);
      
      // Should use --chown in COPY commands
      expect(content, 'Should use --chown for security').toMatch(/--chown=/);
    });

    it(
      formatGWT('Dockerfile runtime', 'define health check', 'HEALTHCHECK is present'),
      () => {
      const content = readFileSync(dockerfile, 'utf8');
      
      expect(content, 'Should have HEALTHCHECK').toMatch(/HEALTHCHECK/);
    });

    it(
      formatGWT('Dockerfile production', 'set NODE_ENV=production', 'environment is configured for prod'),
      () => {
      const content = readFileSync(dockerfile, 'utf8');
      
      expect(content, 'Should set NODE_ENV=production').toMatch(/NODE_ENV=production/);
    });

    it(
      formatGWT('Dockerfile base image', 'use node:*-alpine', 'image size is minimized'),
      () => {
      const content = readFileSync(dockerfile, 'utf8');
      
      expect(content, 'Should use Alpine images').toMatch(/docker\.io\/node:.*-alpine/);
    });
  });

  describe('Docker Ignore Configuration', () => {
    it(
      formatGWT('Docker ignore', 'list comprehensive dev/test paths', 'docker build context is minimized'),
      () => {
      expect(existsSync(dockerignore)).toBe(true);
      
      const content = readFileSync(dockerignore, 'utf8');
      const lines = content.split('\n').map(line => line.trim()).filter(line => line && !line.startsWith('#'));
      
      // Should ignore essential development files
      expect(lines).toContain('node_modules/');
      expect(lines).toContain('tests/');
      expect(lines).toContain('.git/');
      expect(lines).toContain('.github/');
      expect(lines).toContain('coverage/');
      expect(lines).toContain('*.test.ts');
      expect(lines).toContain('README.md');
      expect(lines).toContain('docs/');
    });

    it(
      formatGWT('Docker ignore', 'exclude sensitive files', 'env/keys/secrets are ignored'),
      () => {
      const content = readFileSync(dockerignore, 'utf8');
      
      expect(content, 'Should ignore .env files').toMatch(/\.env/);
      expect(content, 'Should ignore key files').toMatch(/\*\.key/);
      expect(content, 'Should ignore secrets').toMatch(/secrets/);
    });

    it('should have appropriate size (comprehensive but not excessive)', () => {
      const content = readFileSync(dockerignore, 'utf8');
      const lines = content.split('\n').filter(line => line.trim() && !line.trim().startsWith('#'));
      
      expect(lines.length, 'Should have comprehensive ignore list').toBeGreaterThan(20);
      expect(lines.length, 'Should not be excessively long').toBeLessThan(100);
    });
  });

  describe('Docker Compose Configuration', () => {
    it(
      formatGWT('Compose dev', 'define healthcheck/resources/user', 'development compose is present'),
      () => {
      expect(existsSync(dockerCompose)).toBe(true);
      
      const content = readFileSync(dockerCompose, 'utf8');
      
      // Should have health checks
      expect(content, 'Should have healthcheck configuration').toMatch(/healthcheck/);
      
      // Should have resource limits
      expect(content, 'Should have resource limits').toMatch(/resources:/);
      expect(content, 'Should have memory limits').toMatch(/memory:/);
      expect(content, 'Should have CPU limits').toMatch(/cpus:/);
      
      // Should use non-root user
      expect(content, 'Should specify user ID').toMatch(/user:/);
    });

    it(
      formatGWT('Compose prod', 'enable security hardening', 'readonly/cap_drop/security_opt/no-new-privileges present'),
      () => {
      expect(existsSync(dockerComposeProd)).toBe(true);
      
      const content = readFileSync(dockerComposeProd, 'utf8');
      
      // Should have production-specific security
      expect(content, 'Should use read-only filesystem').toMatch(/read_only: true/);
      expect(content, 'Should drop capabilities').toMatch(/cap_drop:/);
      expect(content, 'Should have security options').toMatch(/security_opt:/);
      expect(content, 'Should disable new privileges').toMatch(/no-new-privileges/);
      
      // Should have replicas for high availability
      expect(content, 'Should have multiple replicas').toMatch(/replicas:/);
      
      // Should have restart policy
      expect(content, 'Should have restart policy').toMatch(/restart_policy:/);
    });
  });

  describe('Image Size Optimization', () => {
    it('should have minimal final image structure', () => {
      const content = readFileSync(dockerfile, 'utf8');
      
      // Final stage should only copy necessary files
      const finalStageMatch = content.match(/FROM .* AS runtime[\s\S]*$/);
      expect(finalStageMatch).toBeDefined();
      
      const finalStage = finalStageMatch![0];
      
      // Should copy from build stage, not include source
      expect(finalStage, 'Should copy from build stage').toMatch(/COPY --from=build/);
      expect(finalStage, 'Should not copy source files directly').not.toMatch(/COPY \. \./);
      
      // Should only copy production node_modules
      expect(finalStage, 'Should copy pruned dependencies').toMatch(/node_modules/);
    });
  });

  describe('Security Hardening', () => {
    it('should follow Docker security best practices', () => {
      const content = readFileSync(dockerfile, 'utf8');
      
      // Should not run as root
      expect(content, 'Should not use root user').toMatch(/USER \w+/);
      
      // Should create application directories with proper ownership
      expect(content, 'Should set proper ownership').toMatch(/chown/);
      
      // Should use specific user/group IDs for consistency
      expect(content, 'Should use specific user IDs').toMatch(/1001/);
    });

    it('should have production compose security features', () => {
      const content = readFileSync(dockerComposeProd, 'utf8');
      
      // Security features for production
      const securityFeatures = [
        'read_only: true',
        'cap_drop:',
        'security_opt:',
        'no-new-privileges:true',
        'label=disable',
        'tmpfs:'
      ];
      
      securityFeatures.forEach(feature => {
        expect(content, `Should have ${feature} for security`).toMatch(new RegExp(feature.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')));
      });
    });
  });

  describe('Performance Optimization', () => {
    it('should have resource limits configured', () => {
      const devContent = readFileSync(dockerCompose, 'utf8');
      const prodContent = readFileSync(dockerComposeProd, 'utf8');
      
      // Dev should define baseline limits
      expect(devContent, 'Dev should define resource limits').toMatch(/resources:/);
      expect(devContent, 'Dev should cap memory to 512M').toMatch(/memory:\s*512M/);
      expect(devContent, 'Dev should cap CPU to 0.5').toMatch(/cpus:\s*"0\.5"/);

      // Prod should remain hardened and replicated
      expect(prodContent, 'Prod should remain read-only').toMatch(/read_only: true/);
      expect(prodContent, 'Prod should drop capabilities').toMatch(/cap_drop:/);
      expect(prodContent, 'Prod should use multiple replicas').toMatch(/replicas:\s*2/);
      expect(prodContent, 'Prod should include restart policy').toMatch(/restart_policy/);
    });

    it('should have caching and observability configured', () => {
      const prodContent = readFileSync(dockerComposeProd, 'utf8');
      
      // Should have OpenTelemetry configuration
      expect(prodContent, 'Should have OTEL configuration').toMatch(/OTEL_EXPORTER_OTLP_ENDPOINT/);

      // Should depend on observability collector
      expect(prodContent, 'Should depend on OTEL collector').toMatch(/depends_on:[\s\S]*- otel/);

      // Should mount tmpfs for ephemeral storage
      expect(prodContent, 'Should configure tmpfs').toMatch(/tmpfs:\s*- \/tmp/);
    });
  });
});
