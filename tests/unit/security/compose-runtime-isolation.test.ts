import { readFileSync } from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import YAML from 'yaml';

const COMPOSE_FILES = [
  'docker/docker-compose.yml',
  'docker/docker-compose.test.yml',
  'docker/compose.yaml',
  'podman/compose.dev.yaml',
  'podman/compose.prod.yaml',
  'infra/podman/unit-compose.yml',
] as const;

type ComposeService = {
  environment?: Record<string, unknown> | string[];
  volumes?: Array<string | { type?: string; source?: string; target?: string }>;
};

type ComposeFile = {
  services?: Record<string, ComposeService>;
};

const readCompose = (filePath: string): ComposeFile => YAML.parse(readFileSync(filePath, 'utf8')) as ComposeFile;

const environmentEntries = (environment: ComposeService['environment']): Array<[string, string]> => {
  if (!environment) return [];
  if (Array.isArray(environment)) {
    return environment.map((entry) => {
      const [key, ...valueParts] = String(entry).split('=');
      return [key, valueParts.join('=')];
    });
  }
  return Object.entries(environment).map(([key, value]) => [key, String(value)]);
};

const volumeSource = (volume: string | { source?: string }): string | undefined => {
  if (typeof volume === 'object') return volume.source;
  const [source] = volume.split(':');
  return source;
};

const isSensitiveHostSource = (source: string): boolean => source.startsWith('/')
  || source.startsWith('~')
  || source === '..'
  || source.startsWith('/etc')
  || source.startsWith('/root')
  || source.startsWith('/var/run')
  || source.startsWith('/var/lib/docker')
  || source.startsWith('/var/lib/containers');

const isNamedVolumeSource = (source: string): boolean => /^[A-Za-z0-9][A-Za-z0-9_.-]*$/.test(source);

const isRepoContainedSource = (filePath: string, source: string): boolean => {
  if (isNamedVolumeSource(source)) return true;
  if (path.isAbsolute(source) || source.startsWith('~')) return false;
  const repoRoot = process.cwd();
  const composeDir = path.dirname(path.resolve(repoRoot, filePath));
  const resolvedSource = path.resolve(composeDir, source);
  const relative = path.relative(repoRoot, resolvedSource);
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
};

describe('compose runtime isolation', () => {
  it('TGT-017-F001: does not keep literal database credentials in compose manifests', () => {
    const credentialKey = /(?:POSTGRES_(?:USER|PASSWORD|DB)|DATABASE_URL|.*(?:PASSWORD|SECRET|TOKEN|API_KEY).*)/i;

    for (const filePath of COMPOSE_FILES) {
      const compose = readCompose(filePath);
      for (const [serviceName, service] of Object.entries(compose.services ?? {})) {
        for (const [key, value] of environmentEntries(service.environment)) {
          if (!credentialKey.test(key)) continue;
          expect(value, `${filePath}:${serviceName}.${key} must use environment injection`).toContain('${');
        }
      }
    }
  });

  it('TGT-004-F003: avoids sensitive or absolute host-root bind mounts in compose manifests', () => {
    for (const filePath of COMPOSE_FILES) {
      const compose = readCompose(filePath);
      for (const [serviceName, service] of Object.entries(compose.services ?? {})) {
        for (const volume of service.volumes ?? []) {
          const source = volumeSource(volume);
          if (!source || isNamedVolumeSource(source)) continue;
          expect(isSensitiveHostSource(source), `${filePath}:${serviceName} mounts sensitive host source ${source}`).toBe(false);
          expect(isRepoContainedSource(filePath, source), `${filePath}:${serviceName} host source ${source} must stay inside the repository workspace`).toBe(true);
        }
      }
    }
  });

  it('parses modified compose manifests as YAML', () => {
    for (const filePath of COMPOSE_FILES) {
      expect(() => readCompose(filePath), `${filePath} must be valid YAML`).not.toThrow();
    }
  });

  it('TGT-017-F001: injects test compose credentials in docker-tests workflow without static secrets', () => {
    const workflow = readFileSync('.github/workflows/docker-tests.yml', 'utf8');
    expect(workflow).toContain('AE_TEST_POSTGRES_DB: ae_test_${{ github.run_id }}');
    expect(workflow).toContain('AE_TEST_POSTGRES_USER: ae_test_${{ github.run_id }}');
    expect(workflow).toContain('AE_TEST_POSTGRES_PASSWORD: ae-test-${{ github.run_id }}-${{ github.run_attempt }}');
    expect(workflow).not.toContain('AE_TEST_POSTGRES_PASSWORD: test_password');
  });
});
