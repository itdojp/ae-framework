import { readFileSync } from 'node:fs';
import { extname, resolve } from 'node:path';

import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import yaml from 'yaml';
import { describe, expect, it } from 'vitest';

const schema = JSON.parse(
  readFileSync(resolve('schema/discovery-pack-v1.schema.json'), 'utf8'),
) as Record<string, unknown>;

type DiscoveryPackSection =
  | 'sources'
  | 'actors'
  | 'external_systems'
  | 'goals'
  | 'requirements'
  | 'business_use_cases'
  | 'flows'
  | 'decisions'
  | 'assumptions'
  | 'open_questions';

type DiscoveryPack = {
  sources?: Array<{ id?: string }>;
  actors?: Array<Record<string, unknown>>;
  external_systems?: Array<Record<string, unknown>>;
  goals?: Array<Record<string, unknown>>;
  requirements?: Array<Record<string, unknown>>;
  business_use_cases?: Array<Record<string, unknown>>;
  flows?: Array<Record<string, unknown>>;
  decisions?: Array<Record<string, unknown>>;
  assumptions?: Array<Record<string, unknown>>;
  open_questions?: Array<Record<string, unknown>>;
};

const ELEMENT_SECTIONS: DiscoveryPackSection[] = [
  'actors',
  'external_systems',
  'goals',
  'requirements',
  'business_use_cases',
  'flows',
  'decisions',
  'assumptions',
  'open_questions',
];

const loadFixture = (relativePath: string): DiscoveryPack => {
  const absolutePath = resolve(relativePath);
  const raw = readFileSync(absolutePath, 'utf8');
  const extension = extname(relativePath).toLowerCase();
  if (extension === '.yaml' || extension === '.yml') {
    return yaml.parse(raw) as DiscoveryPack;
  }
  return JSON.parse(raw) as DiscoveryPack;
};

const buildIdIndex = (fixture: DiscoveryPack) => {
  const occurrences = new Map<string, Array<{ section: DiscoveryPackSection; index: number }>>();

  const register = (section: DiscoveryPackSection, id: string | undefined, index: number) => {
    if (!id) {
      return;
    }
    const existing = occurrences.get(id) ?? [];
    existing.push({ section, index });
    occurrences.set(id, existing);
  };

  (fixture.sources ?? []).forEach((entry, index) => register('sources', entry.id, index));
  for (const section of ELEMENT_SECTIONS) {
    const entries = fixture[section] ?? [];
    entries.forEach((entry, index) => register(section, String(entry['id'] ?? ''), index));
  }

  return occurrences;
};

const validateSemanticRefs = (fixture: DiscoveryPack) => {
  const sourceIds = new Set((fixture.sources ?? []).map((entry) => entry.id).filter(Boolean) as string[]);
  const elementIds = new Set<string>();
  for (const section of ELEMENT_SECTIONS) {
    for (const entry of fixture[section] ?? []) {
      const id = entry['id'];
      if (typeof id === 'string' && id.trim()) {
        elementIds.add(id);
      }
    }
  }

  const violations: Array<{ type: string; id: string; ref: string }> = [];

  for (const section of ELEMENT_SECTIONS) {
    for (const entry of fixture[section] ?? []) {
      const id = typeof entry['id'] === 'string' ? entry['id'] : `${section}-unknown`;
      for (const ref of (entry['source_refs'] as string[] | undefined) ?? []) {
        if (!sourceIds.has(ref)) {
          violations.push({ type: 'source-ref-missing', id, ref });
        }
      }
      for (const ref of (entry['traces_to'] as string[] | undefined) ?? []) {
        if (!elementIds.has(ref)) {
          violations.push({ type: 'trace-ref-missing', id, ref });
        }
      }
    }
  }

  return violations;
};

describe('discovery-pack contract', () => {
  it('validates the minimal and rdra-lite sample fixtures', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);

    const fixtures = [
      'fixtures/discovery-pack/minimal.yaml',
      'fixtures/discovery-pack/rdra-lite-sample.yaml',
    ].map(loadFixture);

    for (const fixture of fixtures) {
      expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);
      expect(
        Array.from(buildIdIndex(fixture).values()).every((occurrences) => occurrences.length === 1),
      ).toBe(true);
      expect(validateSemanticRefs(fixture)).toEqual([]);
    }
  });

  it('rejects invalid status values', () => {
    const ajv = new Ajv2020({ allErrors: true, strict: false });
    addFormats(ajv);
    const validate = ajv.compile(schema);
    const fixture = loadFixture('fixtures/discovery-pack/invalid.invalid-status.yaml');

    expect(validate(fixture)).toBe(false);
    expect(
      validate.errors?.some((entry) => entry.instancePath.includes('/actors/0/status')),
    ).toBe(true);
  });

  it('detects duplicate IDs across sections', () => {
    const fixture = loadFixture('fixtures/discovery-pack/invalid.duplicate-id.yaml');
    const duplicateIds = Array.from(buildIdIndex(fixture).entries()).filter(
      ([, occurrences]) => occurrences.length > 1,
    );

    expect(duplicateIds).toEqual([
      [
        'DUPLICATE-ID',
        [
          { section: 'actors', index: 0 },
          { section: 'goals', index: 0 },
        ],
      ],
    ]);
  });

  it('detects missing source_refs and traces_to targets', () => {
    const fixture = loadFixture('fixtures/discovery-pack/invalid.invalid-refs.yaml');

    expect(validateSemanticRefs(fixture)).toEqual([
      {
        type: 'source-ref-missing',
        id: 'ACTOR-WAREHOUSE-CLERK',
        ref: 'SRC-MISSING',
      },
      {
        type: 'trace-ref-missing',
        id: 'ACTOR-WAREHOUSE-CLERK',
        ref: 'GOAL-MISSING',
      },
    ]);
  });
});
