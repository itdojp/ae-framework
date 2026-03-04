function asObject(value) {
  return value && typeof value === 'object' && !Array.isArray(value) ? value : {};
}

function asString(value) {
  return typeof value === 'string' ? value : '';
}

function asStringArray(value) {
  if (!Array.isArray(value)) {
    return undefined;
  }
  const items = value
    .map((entry) => asString(entry).trim())
    .filter(Boolean);
  return items.length > 0 ? items : undefined;
}

function normalizeCorrelation(source) {
  const candidate = asObject(source.correlation);
  const traceCorrelation = asObject(source.traceCorrelation);
  const merged = Object.keys(candidate).length > 0 ? candidate : traceCorrelation;
  const normalized = {
    runId: asString(merged.runId),
    workflow: asString(merged.workflow),
    commit: asString(merged.commit),
    branch: asString(merged.branch),
  };
  const traceIds = asStringArray(merged.traceIds);
  if (traceIds) {
    normalized.traceIds = traceIds;
  }
  return normalized;
}

function normalizeArtifacts(source) {
  const artifacts = Array.isArray(source.artifacts) ? source.artifacts : [];
  return artifacts
    .map((entry) => asObject(entry))
    .filter((entry) => typeof entry.type === 'string' && typeof entry.path === 'string')
    .map((entry) => {
      const normalized = {
        type: entry.type,
        path: entry.path,
      };
      if (entry.checksum === null || typeof entry.checksum === 'string') {
        normalized.checksum = entry.checksum;
      }
      if (entry.description === null || typeof entry.description === 'string') {
        normalized.description = entry.description;
      }
      return normalized;
    });
}

export function toLegacyReportEnvelope(sourceEnvelope) {
  const source = asObject(sourceEnvelope);
  const legacy = {
    schemaVersion: asString(source.schemaVersion) || '1.0.0',
    source: asString(source.source) || 'unknown',
    generatedAt: asString(source.generatedAt),
    correlation: normalizeCorrelation(source),
    summary: asObject(source.summary),
    artifacts: normalizeArtifacts(source),
  };
  if (Array.isArray(source.notes)) {
    legacy.notes = source.notes
      .map((entry) => asString(entry).trim())
      .filter(Boolean);
  }
  return legacy;
}
