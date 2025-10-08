import fs from 'node:fs';

/**
 * Collect unique trace IDs from an NDJSON stream of events.
 * Lines that fail to parse or do not contain a string traceId are skipped.
 * @param {string | null | undefined} ndjsonPath
 * @returns {string[]}
 */
export function collectTraceIdsFromNdjson(ndjsonPath) {
  if (!ndjsonPath || !fs.existsSync(ndjsonPath)) return [];
  const ids = new Set();
  const content = fs.readFileSync(ndjsonPath, 'utf8');
  for (const line of content.split(/\r?\n/)) {
    if (!line.trim()) continue;
    try {
      const event = JSON.parse(line);
      const value = event && typeof event.traceId === 'string' ? event.traceId.trim() : '';
      if (value) ids.add(value);
    } catch (error) {
      // ignore malformed line
    }
  }
  return Array.from(ids);
}

/**
 * Build Tempo explore links for the given trace IDs using the provided template.
 * When no template is supplied the REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE env var is used.
 * @param {string[]} traceIds
 * @param {string | undefined} template
 * @returns {string[]}
 */
export function buildTempoLinks(traceIds, template = process.env.REPORT_ENVELOPE_TEMPO_LINK_TEMPLATE) {
  if (!Array.isArray(traceIds) || traceIds.length === 0) return [];
  const resolved = template?.trim();
  if (!resolved) return [];
  return traceIds.map((id) => {
    const encoded = encodeURIComponent(id);
    if (resolved.includes('{traceId}')) {
      return resolved.replace('{traceId}', encoded);
    }
    const separator = resolved.includes('?') ? '&' : '?';
    return `${resolved}${separator}traceId=${encoded}`;
  });
}
