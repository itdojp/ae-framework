import fs from 'node:fs';
import path from 'node:path';

const WINDOWS_ABSOLUTE_RE = /^[A-Za-z]:[\\/]/;
const CONTROL_CHARS_RE = /[\u0000-\u001f\u007f]/;

function toPosixPath(value) {
  return String(value || '').replace(/\\/g, '/');
}

function isSubpath(candidate, root) {
  const relative = path.relative(root, candidate);
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
}

export function validateChoice(value, { allowed, name, defaultValue }) {
  const selected = String(value || defaultValue || '').trim();
  if (!allowed.includes(selected)) {
    throw new Error(`${name} must be one of: ${allowed.join(', ')}`);
  }
  return selected;
}

export function resolveRepoRelativeFileInput(
  value,
  {
    repoRoot = process.cwd(),
    defaultPath,
    allowedRoots,
    allowedExtensions,
    name = 'file',
  },
) {
  const raw = String(value || defaultPath || '').trim();
  if (!raw) {
    throw new Error(`${name} must not be empty`);
  }
  if (CONTROL_CHARS_RE.test(raw)) {
    throw new Error(`${name} must not contain control characters`);
  }
  if (raw.includes('\\')) {
    throw new Error(`${name} must use POSIX-style repository-relative separators`);
  }
  if (path.isAbsolute(raw) || WINDOWS_ABSOLUTE_RE.test(raw) || raw.startsWith('//')) {
    throw new Error(`${name} must be repository-relative`);
  }

  const normalized = path.posix.normalize(toPosixPath(raw));
  if (normalized === '.' || normalized.startsWith('../') || normalized === '..') {
    throw new Error(`${name} must not contain parent traversal`);
  }

  const extension = path.posix.extname(normalized);
  if (allowedExtensions?.length && !allowedExtensions.includes(extension)) {
    throw new Error(`${name} must use one of these extensions: ${allowedExtensions.join(', ')}`);
  }

  const normalizedAllowedRoots = allowedRoots.map((root) => path.posix.normalize(root).replace(/\/$/, ''));
  const isAllowedRoot = normalizedAllowedRoots.some((root) => normalized === root || normalized.startsWith(`${root}/`));
  if (!isAllowedRoot) {
    throw new Error(`${name} must be under one of: ${normalizedAllowedRoots.join(', ')}`);
  }

  const absolutePath = path.resolve(repoRoot, normalized);
  const absoluteRepoRoot = path.resolve(repoRoot);
  if (!isSubpath(absolutePath, absoluteRepoRoot)) {
    throw new Error(`${name} resolved outside the repository`);
  }

  if (fs.existsSync(absolutePath)) {
    const realFile = fs.realpathSync(absolutePath);
    const allowedRealRoots = normalizedAllowedRoots.map((root) => {
      const candidate = path.resolve(absoluteRepoRoot, root);
      return fs.existsSync(candidate) ? fs.realpathSync(candidate) : candidate;
    });
    if (!allowedRealRoots.some((root) => isSubpath(realFile, root))) {
      throw new Error(`${name} resolved outside the approved directory`);
    }
  }

  return {
    relativePath: normalized,
    absolutePath,
  };
}

export const FORMAL_TARGETS = ['all', 'conformance', 'alloy', 'tla', 'smt', 'apalache', 'kani', 'spin', 'csp', 'lean'];
export const TLA_ENGINES = ['tlc', 'apalache'];
export const SMT_SOLVERS = ['z3', 'cvc5'];
