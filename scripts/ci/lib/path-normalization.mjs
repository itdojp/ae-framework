import path from 'node:path';

const toPosixPath = (value) => String(value).replace(/\\/g, '/');

const looksLikeWindowsAbs = (value) =>
  typeof value === 'string' && (/^[A-Za-z]:[\\/]/.test(value) || value.startsWith('\\\\'));

const normalizeUncPath = (raw) => {
  const posix = toPosixPath(raw);
  const withoutLeadingSlashes = posix.replace(/^\/+/, '');
  const normalizedWithRoot = path.posix.normalize(`/${withoutLeadingSlashes}`);
  const normalized = normalizedWithRoot.replace(/^\/+/, '');
  return `//${normalized}`;
};

/**
 * Normalize a path string for artifacts/reports JSON.
 *
 * Contract (high-level):
 * - Keep relative paths relative (but normalize separators to `/`).
 * - Convert absolute paths under repoRoot to repo-relative.
 * - Keep absolute paths outside repoRoot as absolute (but normalize separators to `/`).
 */
export function normalizeArtifactPath(value, { repoRoot = process.cwd() } = {}) {
  if (value === null || value === undefined) return null;
  const raw = String(value).trim();
  if (!raw) return null;

  // Preserve UNC semantics: `\\server\share\...` should become `//server/share/...` after normalization.
  if (raw.startsWith('\\\\') || raw.startsWith('//')) {
    if (path.isAbsolute(raw)) {
      const root = path.resolve(repoRoot);
      const abs = path.resolve(raw);
      const rel = path.relative(root, abs);
      if (!rel.startsWith('..') && !path.isAbsolute(rel)) {
        return path.posix.normalize(toPosixPath(rel));
      }
    }
    return normalizeUncPath(raw);
  }

  // On POSIX hosts, Windows absolute paths are treated as external absolute paths (portable representation only).
  // On Windows hosts, we let `path.isAbsolute()` handle them so they can become repo-relative when applicable.
  if (looksLikeWindowsAbs(raw) && !path.isAbsolute(raw)) {
    return path.posix.normalize(toPosixPath(raw));
  }

  // POSIX absolute path: convert to repo-relative when inside repoRoot.
  if (path.isAbsolute(raw)) {
    const root = path.resolve(repoRoot);
    const abs = path.resolve(raw);
    const rel = path.relative(root, abs);
    if (!rel.startsWith('..') && !path.isAbsolute(rel)) {
      return path.posix.normalize(toPosixPath(rel));
    }
    return path.posix.normalize(toPosixPath(abs));
  }

  // Relative path: keep it relative but normalize separators and redundant segments.
  return path.posix.normalize(toPosixPath(raw));
}
