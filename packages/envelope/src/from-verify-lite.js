const DEFAULT_SCHEMA_VERSION = '1.0.0';
const DEFAULT_SOURCE = 'verify-lite';

const ARTIFACT_DESCRIPTIONS = {
  lintSummary: 'Lint summary',
  lintLog: 'Lint log',
  mutationSummary: 'Mutation summary',
  mutationSurvivors: 'Mutation survivors',
  conformanceSummary: 'Conformance summary',
  conformanceSummaryMarkdown: 'Conformance summary (markdown)',
};

const isNonEmptyString = (value) => typeof value === 'string' && value.trim().length > 0;

const cloneSummary = (summary) => {
  if (typeof structuredClone === 'function') {
    return structuredClone(summary);
  }
  return JSON.parse(JSON.stringify(summary));
};

const collectTraceIds = (summary, seed = []) => {
  const ids = new Set(seed.filter(isNonEmptyString));

  const append = (values) => {
    if (!Array.isArray(values)) return;
    for (const value of values) {
      if (isNonEmptyString(value)) {
        ids.add(value.trim());
      }
    }
  };

  append(summary?.trace?.traceIds);
  if (Array.isArray(summary?.trace?.domains)) {
    for (const domain of summary.trace.domains) {
      append(domain?.traceIds);
    }
  }

  return Array.from(ids);
};

const collectTempoLinks = (summary, traceIds, provided = [], template) => {
  const links = new Set();

  const add = (values) => {
    if (!Array.isArray(values)) return;
    for (const value of values) {
      if (isNonEmptyString(value)) {
        links.add(value.trim());
      }
    }
  };

  add(summary?.tempoLinks);
  add(summary?.trace?.tempoLinks);
  if (Array.isArray(summary?.trace?.domains)) {
    for (const domain of summary.trace.domains) {
      add(domain?.tempoLinks);
    }
  }
  add(provided);

  if (template && template.includes('{traceId}')) {
    for (const id of traceIds) {
      links.add(template.replace('{traceId}', id));
    }
  }

  return Array.from(links);
};

const buildArtifact = (value, key) => {
  if (!isNonEmptyString(value)) {
    return null;
  }
  const artifact = {
    type: 'application/json',
    path: value,
  };
  const description = ARTIFACT_DESCRIPTIONS[key];
  if (description) {
    artifact.description = description;
  }
  return artifact;
};

const extractArtifacts = (artifacts, extra = []) => {
  const items = [];
  for (const [key, value] of Object.entries(artifacts ?? {})) {
    const artifact = buildArtifact(value, key);
    if (artifact) {
      items.push(artifact);
    }
  }
  for (const artifact of extra) {
    if (artifact && isNonEmptyString(artifact.path)) {
      items.push(artifact);
    }
  }
  return items;
};

const mergeNotes = (tempoLinks, notes) => {
  const merged = [];
  if (Array.isArray(notes)) {
    for (const note of notes) {
      if (isNonEmptyString(note)) {
        merged.push(note.trim());
      }
    }
  }
  for (const link of tempoLinks) {
    merged.push(`Tempo: ${link}`);
  }
  return Array.from(new Set(merged));
};

export function fromVerifyLite(summary, options) {
  const summaryClone = cloneSummary(summary);
  const generatedAt = options.generatedAt ?? new Date().toISOString();
  const source = options.source ?? DEFAULT_SOURCE;

  const traceIds = collectTraceIds(summaryClone, options.correlation.traceIds ?? []);
  const tempoLinks = collectTempoLinks(
    summaryClone,
    traceIds,
    options.tempoLinks ?? [],
    options.tempoLinkTemplate,
  );

  if (summaryClone.trace) {
    if (!Array.isArray(summaryClone.trace.traceIds) || summaryClone.trace.traceIds.length === 0) {
      summaryClone.trace = { ...summaryClone.trace, traceIds };
    }
    if (!Array.isArray(summaryClone.trace.tempoLinks) || summaryClone.trace.tempoLinks.length === 0) {
      summaryClone.trace = { ...summaryClone.trace, tempoLinks };
    }
  } else if (traceIds.length > 0 || tempoLinks.length > 0) {
    summaryClone.trace = {};
    if (traceIds.length > 0) {
      summaryClone.trace.traceIds = traceIds;
    }
    if (tempoLinks.length > 0) {
      summaryClone.trace.tempoLinks = tempoLinks;
    }
  }

  const artifacts = extractArtifacts(summaryClone.artifacts, options.extraArtifacts);
  const notes = mergeNotes(tempoLinks, options.notes);

  const correlation = {
    runId: options.correlation.runId,
    ...(options.correlation.workflow ? { workflow: options.correlation.workflow } : {}),
    ...(options.correlation.commit ? { commit: options.correlation.commit } : {}),
    ...(options.correlation.branch ? { branch: options.correlation.branch } : {}),
    ...(traceIds.length > 0 ? { traceIds } : {}),
  };

  const envelope = {
    schemaVersion: DEFAULT_SCHEMA_VERSION,
    source,
    generatedAt,
    traceCorrelation: correlation,
    summary: summaryClone,
    artifacts,
    ...(tempoLinks.length > 0 ? { tempoLinks } : {}),
    ...(notes.length > 0 ? { notes } : {}),
  };

  if (!('correlation' in envelope)) {
    envelope.correlation = correlation;
  }

  return envelope;
}
