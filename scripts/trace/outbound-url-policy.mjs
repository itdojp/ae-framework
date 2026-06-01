const LOCALHOST_NAMES = new Set(['localhost', '127.0.0.1', '::1', '[::1]']);

function toAllowedHostEntries(rawAllowedHosts) {
  if (!rawAllowedHosts) return new Set();
  const entries = new Set();
  for (const rawEntry of String(rawAllowedHosts).split(/[\s,]+/)) {
    const entry = rawEntry.trim().toLowerCase();
    if (!entry) continue;
    try {
      const parsed = new URL(entry);
      if (parsed.hostname) entries.add(parsed.hostname.toLowerCase());
      if (parsed.host) entries.add(parsed.host.toLowerCase());
      continue;
    } catch {
      // Plain host or host:port allowlist entries are accepted below.
    }
    entries.add(entry);
  }
  return entries;
}

function isLocalhost(url) {
  return LOCALHOST_NAMES.has(url.hostname.toLowerCase());
}

function matchesAllowedHost(url, allowedHosts) {
  const hostname = url.hostname.toLowerCase();
  const host = url.host.toLowerCase();
  return allowedHosts.has(hostname) || allowedHosts.has(host);
}

export function validateTokenBearingUrl(rawUrl, {
  serviceName,
  allowedHostsEnv,
  allowedHosts,
  allowLocalhostHttp = false,
} = {}) {
  const label = serviceName ?? 'outbound integration';
  let url;
  try {
    url = new URL(rawUrl);
  } catch {
    throw new Error(`${label} URL is malformed`);
  }

  if (url.username || url.password) {
    throw new Error(`${label} URL must not contain userinfo`);
  }
  if (!url.hostname) {
    throw new Error(`${label} URL must include a hostname`);
  }
  if (url.protocol !== 'https:' && !(allowLocalhostHttp && url.protocol === 'http:' && isLocalhost(url))) {
    throw new Error(`${label} URL must use HTTPS${allowLocalhostHttp ? ' unless it is localhost HTTP for development' : ''}`);
  }

  if (allowLocalhostHttp && isLocalhost(url)) {
    return url;
  }

  const allowed = allowedHosts ?? toAllowedHostEntries(allowedHostsEnv ? process.env[allowedHostsEnv] : '');
  if (!matchesAllowedHost(url, allowed)) {
    const envMessage = allowedHostsEnv ? ` via ${allowedHostsEnv}` : '';
    throw new Error(`${label} host must be explicitly allowlisted${envMessage}`);
  }

  return url;
}

export function sanitizeExternalResponseText(value, maxLength = 500) {
  const normalized = String(value ?? '')
    .replace(/[\u0000-\u001f\u007f]+/g, ' ')
    .replace(/Bearer\s+[A-Za-z0-9._~+/=-]+/gi, 'Bearer [REDACTED]')
    .replace(/(api[_-]?key|token|password|secret|authorization)=([^&\s]+)/gi, '$1=[REDACTED]')
    .trim();
  if (normalized.length <= maxLength) {
    return normalized;
  }
  return `${normalized.slice(0, maxLength)}…[truncated]`;
}

export const __test__ = {
  toAllowedHostEntries,
};
