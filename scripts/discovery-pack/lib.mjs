import fs from 'node:fs';
import path from 'node:path';

import { globSync } from 'glob';
import yaml from 'yaml';

export const DEFAULT_SOURCES = ['spec/discovery-pack/**/*.{yml,yaml,json}'];
export const DISCOVERY_PACK_SECTIONS = [
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

const normalizePath = (value) => value.replace(/\\/g, '/');
export const toRelativePath = (absolutePath, cwd = process.cwd()) =>
  normalizePath(path.relative(cwd, absolutePath) || '.');

export const parseYamlOrJson = (sourcePath) => {
  const raw = fs.readFileSync(sourcePath, 'utf8');
  const lowerPath = sourcePath.toLowerCase();
  if (lowerPath.endsWith('.yaml') || lowerPath.endsWith('.yml')) {
    return yaml.parse(raw);
  }
  return JSON.parse(raw);
};

export const splitSourcePatterns = (rawValue) => {
  const chunks = [];
  let buffer = '';
  let braceDepth = 0;
  for (const char of rawValue) {
    if (char === '{') {
      braceDepth += 1;
      buffer += char;
      continue;
    }
    if (char === '}') {
      braceDepth = Math.max(0, braceDepth - 1);
      buffer += char;
      continue;
    }
    if (char === ',' && braceDepth === 0) {
      chunks.push(buffer);
      buffer = '';
      continue;
    }
    buffer += char;
  }
  chunks.push(buffer);
  return chunks;
};

export const discoverSources = (sourcePatterns) => {
  const matches = new Set();
  for (const pattern of sourcePatterns) {
    for (const sourcePath of globSync(pattern, { nodir: true })) {
      matches.add(path.resolve(sourcePath));
    }
  }
  return Array.from(matches).sort((a, b) => a.localeCompare(b));
};

export const collectEntries = (pack) => {
  const entries = [];
  for (const section of DISCOVERY_PACK_SECTIONS) {
    const sectionEntries = Array.isArray(pack?.[section]) ? pack[section] : [];
    sectionEntries.forEach((entry, index) => {
      entries.push({ section, index, entry });
    });
  }
  return entries;
};

export const analyzeDiscoveryPackSemantics = (pack, options = {}) => {
  const strictApproved = options.strictApproved === true;
  const allIdOccurrences = new Map();
  const sourceIds = new Set();
  const entryStatuses = new Map();
  const inboundRefCounts = new Map();
  const errors = [];
  const warnings = [];

  const registerOccurrence = (id, section, index) => {
    const occurrences = allIdOccurrences.get(id) ?? [];
    occurrences.push({ section, index });
    allIdOccurrences.set(id, occurrences);
  };

  (Array.isArray(pack?.sources) ? pack.sources : []).forEach((source, index) => {
    const id = typeof source?.id === 'string' ? source.id.trim() : '';
    if (!id) {
      return;
    }
    sourceIds.add(id);
    registerOccurrence(id, 'sources', index);
  });

  const entries = collectEntries(pack);
  for (const { section, index, entry } of entries) {
    const id = typeof entry?.id === 'string' ? entry.id.trim() : '';
    if (!id) {
      continue;
    }
    registerOccurrence(id, section, index);
    entryStatuses.set(id, typeof entry?.status === 'string' ? entry.status : '');
    inboundRefCounts.set(id, 0);
  }

  for (const [id, occurrences] of allIdOccurrences.entries()) {
    if (occurrences.length > 1) {
      errors.push({
        type: 'duplicate-id',
        id,
        occurrences,
        message: `ID "${id}" is used more than once`,
      });
    }
  }

  for (const { section, index, entry } of entries) {
    const id = typeof entry?.id === 'string' ? entry.id.trim() : `${section}[${index}]`;
    const sourceRefs = Array.isArray(entry?.source_refs) ? entry.source_refs : [];
    const traceRefs = Array.isArray(entry?.traces_to) ? entry.traces_to : [];
    const status = typeof entry?.status === 'string' ? entry.status : '';

    for (const ref of sourceRefs) {
      if (!sourceIds.has(ref)) {
        errors.push({
          type: 'source-ref-missing',
          section,
          id,
          ref,
          message: `source_refs contains unknown source id "${ref}"`,
        });
      }
    }

    for (const ref of traceRefs) {
      if (!entryStatuses.has(ref)) {
        errors.push({
          type: 'trace-ref-missing',
          section,
          id,
          ref,
          message: `traces_to contains unknown discovery element id "${ref}"`,
        });
        continue;
      }

      inboundRefCounts.set(ref, (inboundRefCounts.get(ref) ?? 0) + 1);
      const targetStatus = entryStatuses.get(ref);

      if (status === 'approved' && targetStatus === 'rejected') {
        errors.push({
          type: 'approved-depends-on-rejected',
          section,
          id,
          ref,
          message: `approved element "${id}" depends on rejected element "${ref}"`,
        });
      }

      if (strictApproved && status === 'approved' && targetStatus !== 'approved') {
        errors.push({
          type: 'strict-approved-target-not-approved',
          section,
          id,
          ref,
          message: `approved element "${id}" depends on non-approved element "${ref}" in strict-approved mode`,
        });
      }
    }
  }

  const openQuestions = Array.isArray(pack?.open_questions) ? pack.open_questions : [];
  openQuestions.forEach((entry, index) => {
    const status = typeof entry?.status === 'string' ? entry.status : '';
    if (entry?.blocking === true && status !== 'rejected' && status !== 'deferred') {
      warnings.push({
        type: 'blocking-open-question',
        section: 'open_questions',
        id: typeof entry?.id === 'string' ? entry.id : `open_questions[${index}]`,
        message: 'blocking open question remains unresolved',
      });
    }
  });

  const findOrphans = (section) => {
    const sectionEntries = Array.isArray(pack?.[section]) ? pack[section] : [];
    sectionEntries.forEach((entry, index) => {
      const id = typeof entry?.id === 'string' ? entry.id.trim() : '';
      const status = typeof entry?.status === 'string' ? entry.status : '';
      if (!id || status !== 'approved') {
        return;
      }
      if ((inboundRefCounts.get(id) ?? 0) === 0) {
        warnings.push({
          type: section === 'requirements'
            ? 'orphan-approved-requirement'
            : 'orphan-approved-business-use-case',
          section,
          id: id || `${section}[${index}]`,
          message: `approved ${section === 'requirements' ? 'requirement' : 'business use case'} is not referenced by other discovery elements`,
        });
      }
    });
  };

  findOrphans('requirements');
  findOrphans('business_use_cases');

  return {
    errors,
    warnings,
    summary: {
      duplicateIds: errors.filter((entry) => entry.type === 'duplicate-id').length,
      unresolvedSourceRefs: errors.filter((entry) => entry.type === 'source-ref-missing').length,
      unresolvedTraceRefs: errors.filter((entry) => entry.type === 'trace-ref-missing').length,
      approvedDependsOnRejected: errors.filter((entry) => entry.type === 'approved-depends-on-rejected').length,
      strictApprovedViolations: errors.filter((entry) => entry.type === 'strict-approved-target-not-approved').length,
      blockingOpenQuestions: warnings.filter((entry) => entry.type === 'blocking-open-question').length,
      orphanApprovedRequirements: warnings.filter((entry) => entry.type === 'orphan-approved-requirement').length,
      orphanApprovedBusinessUseCases: warnings.filter((entry) => entry.type === 'orphan-approved-business-use-case').length,
    },
  };
};
