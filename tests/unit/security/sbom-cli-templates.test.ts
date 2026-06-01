import { describe, expect, it } from 'vitest';
import { SBOMCLI } from '../../../src/cli/sbom-cli.js';

type SBOMTemplateAccess = {
  generateGitHubWorkflow(): string;
  generateGitLabPipeline(): string;
  generateJenkinsfile(): string;
};

const createTemplateAccess = (): SBOMTemplateAccess => new SBOMCLI() as unknown as SBOMTemplateAccess;

describe('SBOM CI integration templates', () => {
  it('validates Dependency Track destinations before sending API keys', () => {
    const cli = createTemplateAccess();
    const templates = [
      cli.generateGitHubWorkflow(),
      cli.generateGitLabPipeline(),
      cli.generateJenkinsfile(),
    ];

    for (const template of templates) {
      expect(template).toContain('DEPENDENCY_TRACK_ALLOWED_HOSTS');
      expect(template).toContain('process.argv.slice(1)');
      expect(template).toContain('Dependency Track URL must use HTTPS');
      expect(template).toContain('Dependency Track URL must not contain userinfo');
      expect(template).toContain('Dependency Track URL must include a hostname');
      expect(template).toContain('Dependency Track host must be allowlisted via DEPENDENCY_TRACK_ALLOWED_HOSTS');
      expect(template.indexOf('node -e')).toBeGreaterThanOrEqual(0);
      expect(template.indexOf('node -e')).toBeLessThan(template.indexOf('X-API-Key'));
      expect(template).toContain("--proto '=https'");
      expect(template).toContain('--fail --show-error --silent');
      expect(template).not.toMatch(/curl[^\n]+\$\{?DEPENDENCY_TRACK_URL\}?\/api\/v1\/bom/);
    }
  });
});
