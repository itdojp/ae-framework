import fs from 'node:fs';
import path from 'node:path';
import type { AEIR } from '../../packages/spec-compiler/src/types.js';
import { toMessage } from '../utils/error-utils.js';

type ExportOptions = {
  inputPath: string;
  format: 'kiro';
  outputDir?: string;
  specId?: string;
};

const sanitizeId = (value: string): string =>
  value
    .toLowerCase()
    .replace(/[^a-z0-9._-]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .slice(0, 64) || 'spec';

const renderList = (items: string[], emptyLabel: string): string[] => {
  if (!items.length) {
    return [`- ${emptyLabel}`];
  }
  return items.map((item) => `- ${item}`);
};

const renderUsecases = (usecases?: AEIR['usecases']): string[] => {
  if (!usecases?.length) return ['- (no use cases defined)'];
  return usecases.map((usecase) => {
    const actor = usecase.actor ? ` (actor: ${usecase.actor})` : '';
    const desc = usecase.description ? ` - ${usecase.description}` : '';
    return `- ${usecase.name}${actor}${desc}`;
  });
};

const renderInvariants = (invariants?: AEIR['invariants']): string[] => {
  if (!invariants?.length) return ['- (no invariants defined)'];
  return invariants.map((inv) => `- ${inv.id}: ${inv.description}`);
};

const renderApi = (api?: AEIR['api']): string[] => {
  if (!api?.length) return ['- (no API endpoints defined)'];
  return api.map((endpoint) => {
    const summary = endpoint.summary ? ` - ${endpoint.summary}` : '';
    return `- ${endpoint.method} ${endpoint.path}${summary}`;
  });
};

const renderDomain = (domain: AEIR['domain']): string[] => {
  if (!domain?.length) return ['- (no domain entities defined)'];
  return domain.map((entity) => {
    const fields = entity.fields.map((field) => `${field.name}:${field.type}`).join(', ');
    const desc = entity.description ? ` - ${entity.description}` : '';
    return `- ${entity.name}${desc}${fields ? ` (fields: ${fields})` : ''}`;
  });
};

const renderNfr = (nfr?: AEIR['nfr']): string[] => {
  if (!nfr) return ['- (no NFR defined)'];
  const lines: string[] = [];
  if (nfr.performance) {
    lines.push('- Performance');
    if (nfr.performance.responseTime) {
      Object.entries(nfr.performance.responseTime).forEach(([key, value]) => {
        lines.push(`  - responseTime ${key}: ${value}ms`);
      });
    }
    if (nfr.performance.throughput) {
      Object.entries(nfr.performance.throughput).forEach(([key, value]) => {
        lines.push(`  - throughput ${key}: ${value}rps`);
      });
    }
    if (nfr.performance.concurrency !== undefined) {
      lines.push(`  - concurrency: ${nfr.performance.concurrency}`);
    }
  }
  if (nfr.security) {
    lines.push('- Security');
    if (nfr.security.authentication?.length) {
      lines.push(`  - authentication: ${nfr.security.authentication.join(', ')}`);
    }
    if (nfr.security.authorization?.length) {
      lines.push(`  - authorization: ${nfr.security.authorization.join(', ')}`);
    }
    if (nfr.security.encryption?.length) {
      lines.push(`  - encryption: ${nfr.security.encryption.join(', ')}`);
    }
  }
  if (nfr.reliability) {
    lines.push('- Reliability');
    if (nfr.reliability.availability !== undefined) {
      lines.push(`  - availability: ${nfr.reliability.availability}`);
    }
    if (nfr.reliability.recovery) {
      lines.push(`  - recovery: ${nfr.reliability.recovery}`);
    }
  }
  if (nfr.scalability) {
    lines.push('- Scalability');
    if (nfr.scalability.users !== undefined) {
      lines.push(`  - users: ${nfr.scalability.users}`);
    }
    if (nfr.scalability.dataSize) {
      lines.push(`  - dataSize: ${nfr.scalability.dataSize}`);
    }
  }
  return lines.length ? lines : ['- (no NFR defined)'];
};

const renderTasks = (ir: AEIR): string[] => {
  const lines: string[] = [];
  const usecases = ir.usecases ?? [];
  if (usecases.length) {
    lines.push('## Use Cases');
    usecases.forEach((usecase) => {
      lines.push(`- [ ] Implement use case: ${usecase.name}`);
    });
    lines.push('');
  }
  const invariants = ir.invariants ?? [];
  if (invariants.length) {
    lines.push('## Invariants');
    invariants.forEach((inv) => {
      lines.push(`- [ ] Enforce invariant ${inv.id}: ${inv.description}`);
    });
    lines.push('');
  }
  const api = ir.api ?? [];
  if (api.length) {
    lines.push('## API');
    api.forEach((endpoint) => {
      lines.push(`- [ ] Implement API ${endpoint.method} ${endpoint.path}`);
    });
    lines.push('');
  }
  if (!lines.length) {
    lines.push('- [ ] Define tasks for this spec');
  }
  return lines;
};

export function exportKiroSpec(options: ExportOptions): { outputDir: string; specId: string; files: string[] } {
  const { inputPath, format, outputDir, specId } = options;
  if (format !== 'kiro') {
    throw new Error(`Unsupported export format: ${format}`);
  }

  let ir: AEIR;
  try {
    const raw = fs.readFileSync(inputPath, 'utf8');
    ir = JSON.parse(raw) as AEIR;
  } catch (error) {
    throw new Error(`Failed to read AE-IR: ${toMessage(error)}`);
  }

  const derivedId = specId ? sanitizeId(specId) : sanitizeId(ir.metadata?.name ?? 'spec');
  const targetDir = outputDir ? outputDir : path.join('.kiro', 'specs', derivedId);
  const now = new Date().toISOString();

  fs.mkdirSync(targetDir, { recursive: true });
  fs.mkdirSync(path.join(targetDir, 'assets'), { recursive: true });

  const requirements = [
    '---',
    `specId: ${derivedId}`,
    `version: ${ir.metadata?.version ?? '1.0.0'}`,
    `generatedAt: ${now}`,
    '---',
    '',
    '# Requirements',
    '',
    '## Overview',
    `- Name: ${ir.metadata?.name ?? 'unknown'}`,
    `- Description: ${ir.metadata?.description ?? 'n/a'}`,
    '',
    '## Use Cases',
    ...renderUsecases(ir.usecases),
    '',
    '## Invariants',
    ...renderInvariants(ir.invariants),
    '',
    '## API',
    ...renderApi(ir.api),
    '',
  ].join('\n');

  const design = [
    '# Design',
    '',
    '## Domain Model',
    ...renderDomain(ir.domain),
    '',
    '## Non-Functional Requirements',
    ...renderNfr(ir.nfr),
    '',
    '## Notes',
    '- (add architecture notes, diagrams, and assets in ./assets)',
    '',
  ].join('\n');

  const tasks = [
    '# Tasks',
    '',
    ...renderTasks(ir),
  ].join('\n');

  const files = [
    { name: 'requirements.md', contents: requirements },
    { name: 'design.md', contents: design },
    { name: 'tasks.md', contents: tasks },
  ];

  for (const file of files) {
    fs.writeFileSync(path.join(targetDir, file.name), file.contents);
  }

  return { outputDir: targetDir, specId: derivedId, files: files.map((file) => file.name) };
}
