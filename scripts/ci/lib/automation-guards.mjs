const DEFAULT_DOCS_ALLOWLIST = [/^docs\//, /^README\.md$/];

function parseActorCsv(raw, fallbackRaw = '') {
  const source = String(raw || '').trim() ? String(raw || '') : String(fallbackRaw || '');
  return source
    .split(',')
    .map((value) => value.trim())
    .filter(Boolean);
}

function toActorSet(actors) {
  return new Set(
    (Array.isArray(actors) ? actors : [])
      .map((value) => String(value || '').trim().toLowerCase())
      .filter(Boolean),
  );
}

function isActorAllowed(actor, actorSet) {
  const normalized = String(actor || '').trim().toLowerCase();
  if (!normalized) return false;
  return actorSet instanceof Set && actorSet.has(normalized);
}

function normalizeLabelNames(labels) {
  if (!Array.isArray(labels)) return [];
  return labels
    .map((label) => {
      if (typeof label === 'string') return label;
      if (label && typeof label.name === 'string') return label.name;
      return '';
    })
    .map((name) => name.trim())
    .filter(Boolean);
}

function hasLabel(labels, targetLabel) {
  const target = String(targetLabel || '').trim();
  if (!target) return false;
  return Array.isArray(labels) && labels.includes(target);
}

function isDocsPath(filePath, allowlist = DEFAULT_DOCS_ALLOWLIST) {
  const target = String(filePath || '');
  if (!target) return false;
  return allowlist.some((rule) => rule.test(target));
}

function collectNonDocs(paths, allowlist = DEFAULT_DOCS_ALLOWLIST) {
  const values = Array.isArray(paths) ? paths : [];
  return values
    .map((value) => String(value || ''))
    .filter(Boolean)
    .filter((value) => !isDocsPath(value, allowlist));
}

export {
  DEFAULT_DOCS_ALLOWLIST,
  collectNonDocs,
  hasLabel,
  isActorAllowed,
  isDocsPath,
  normalizeLabelNames,
  parseActorCsv,
  toActorSet,
};
