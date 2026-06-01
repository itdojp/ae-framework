import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import YAML from 'yaml';

type ComposeService = {
  environment?: Record<string, unknown> | string[];
  expose?: Array<string | number>;
  ports?: Array<string | number | Record<string, unknown>>;
};

type ComposeFile = {
  services?: Record<string, ComposeService>;
};

const PROD_COMPOSE_FILES = [
  'docker/docker-compose.prod.yml',
  'podman/compose.prod.yaml',
] as const;

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

const isVariableExpansion = (value: string): boolean => /^\$\{[A-Z0-9_]+(?::[-?][^}]*)?\}$/.test(value);

const portBindingHost = (binding: string | number | Record<string, unknown>): string => {
  if (typeof binding === 'number') return '0.0.0.0';
  if (typeof binding === 'object') {
    const hostIp = binding.host_ip ?? binding.hostIp ?? binding.ip;
    return hostIp ? String(hostIp) : '0.0.0.0';
  }
  const value = String(binding);
  if (value.startsWith('[')) {
    const closing = value.indexOf(']');
    return closing >= 0 && value[closing + 1] === ':' ? value.slice(1, closing) : '0.0.0.0';
  }
  const parts = value.split(':');
  if (parts.length >= 3) return parts[0];
  return '0.0.0.0';
};

const isLoopbackHost = (host: string): boolean => ['127.0.0.1', 'localhost', '::1'].includes(host);

describe('production compose security', () => {
  it('requires externalized Podman production PostgreSQL settings', () => {
    const compose = readCompose('podman/compose.prod.yaml');
    const db = compose.services?.db;
    expect(db).toBeDefined();
    const env = Object.fromEntries(environmentEntries(db?.environment));

    expect(env.POSTGRES_USER).toMatch(/^\$\{POSTGRES_USER:\?/);
    expect(env.POSTGRES_PASSWORD).toMatch(/^\$\{POSTGRES_PASSWORD:\?/);
    expect(env.POSTGRES_DB).toMatch(/^\$\{POSTGRES_DB:\?/);
    expect(env.POSTGRES_PASSWORD).not.toBe('app');
  });

  it('does not keep literal production database credential-like values in prod compose files', () => {
    const credentialKey = /(?:POSTGRES_(?:USER|PASSWORD|DB)|DATABASE_URL|.*(?:PASSWORD|SECRET|TOKEN|API_KEY).*)/i;

    for (const filePath of PROD_COMPOSE_FILES) {
      const compose = readCompose(filePath);
      for (const [serviceName, service] of Object.entries(compose.services ?? {})) {
        for (const [key, value] of environmentEntries(service.environment)) {
          if (!credentialKey.test(key)) continue;
          expect(isVariableExpansion(value), `${filePath}:${serviceName}.${key} must use environment expansion`).toBe(true);
        }
      }
    }
  });

  it('keeps internal production data and telemetry services off non-loopback host ports', () => {
    const internalServices = new Set(['db', 'redis', 'otel', 'otel-collector']);

    for (const filePath of PROD_COMPOSE_FILES) {
      const compose = readCompose(filePath);
      for (const [serviceName, service] of Object.entries(compose.services ?? {})) {
        if (!internalServices.has(serviceName)) continue;
        for (const binding of service.ports ?? []) {
          expect(isLoopbackHost(portBindingHost(binding)), `${filePath}:${serviceName} publishes ${JSON.stringify(binding)} to a non-loopback host`).toBe(true);
        }
      }
    }
  });

  it('documents internal-only production service ports through expose', () => {
    const docker = readCompose('docker/docker-compose.prod.yml');
    expect(docker.services?.['otel-collector']?.expose).toEqual(expect.arrayContaining(['4317', '4318', '8889']));
    expect(docker.services?.redis?.expose).toEqual(expect.arrayContaining(['6379']));

    const podman = readCompose('podman/compose.prod.yaml');
    expect(podman.services?.otel?.expose).toEqual(expect.arrayContaining(['4317', '4318']));
  });
});
