import { execSync } from 'node:child_process';

const pad2 = (value) => String(value).padStart(2, '0');
const pad3 = (value) => String(value).padStart(3, '0');

const formatOffset = (minutes) => {
  const sign = minutes <= 0 ? '+' : '-';
  const abs = Math.abs(minutes);
  const hours = pad2(Math.floor(abs / 60));
  const mins = pad2(abs % 60);
  return `${sign}${hours}:${mins}`;
};

const formatLocalIso = (date) => {
  const year = date.getFullYear();
  const month = pad2(date.getMonth() + 1);
  const day = pad2(date.getDate());
  const hours = pad2(date.getHours());
  const mins = pad2(date.getMinutes());
  const secs = pad2(date.getSeconds());
  const millis = pad3(date.getMilliseconds());
  const offset = formatOffset(date.getTimezoneOffset());
  return `${year}-${month}-${day}T${hours}:${mins}:${secs}.${millis}${offset}`;
};

const pickFirst = (...values) =>
  values.find((value) => value !== undefined && value !== null && String(value).length > 0) ?? null;

const readGit = (cmd) => {
  try {
    return execSync(cmd, { stdio: ['ignore', 'pipe', 'ignore'] })
      .toString()
      .trim();
  } catch {
    return null;
  }
};

const resolveCommit = () =>
  pickFirst(
    process.env.GIT_COMMIT,
    process.env.GITHUB_SHA,
    process.env.COMMIT_SHA,
    readGit('git rev-parse HEAD')
  );

const resolveBranch = () => {
  const envBranch = pickFirst(
    process.env.GITHUB_HEAD_REF,
    process.env.GITHUB_REF_NAME,
    process.env.BRANCH_NAME,
    process.env.GIT_BRANCH
  );
  if (envBranch) return envBranch;
  const ref = process.env.GITHUB_REF;
  if (ref) {
    const match = ref.match(/^refs\/(?:heads|tags)\/(.+)$/);
    if (match) return match[1];
  }
  const branch = readGit('git rev-parse --abbrev-ref HEAD');
  if (branch && branch !== 'HEAD') return branch;
  return null;
};

const normalizeToolVersions = (versions) => {
  const normalized = {};
  for (const [key, value] of Object.entries(versions ?? {})) {
    if (typeof value === 'string' && value.trim().length > 0) {
      normalized[key] = value.trim();
    }
  }
  return normalized;
};

export const buildArtifactMetadata = ({ now = new Date(), toolVersions = {} } = {}) => {
  const date = now instanceof Date ? now : new Date(now);
  const timezoneOffset = formatOffset(date.getTimezoneOffset());
  const runnerName = pickFirst(process.env.RUNNER_NAME, process.env.HOSTNAME);
  const baseToolVersions = { node: process.version };
  const mergedToolVersions = {
    ...baseToolVersions,
    ...normalizeToolVersions(toolVersions)
  };

  return {
    generatedAtUtc: date.toISOString(),
    generatedAtLocal: formatLocalIso(date),
    timezoneOffset,
    gitCommit: resolveCommit(),
    branch: resolveBranch(),
    runner: {
      name: runnerName ?? null,
      os: process.env.RUNNER_OS ?? process.platform,
      arch: process.env.RUNNER_ARCH ?? process.arch,
      ci: process.env.CI === 'true'
    },
    toolVersions: mergedToolVersions
  };
};
