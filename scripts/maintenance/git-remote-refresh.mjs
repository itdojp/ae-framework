export const deriveRemoteFromBaseRef = (baseRef) => {
  const value = String(baseRef || '').trim();
  if (!value) return '';
  if (value.startsWith('refs/remotes/')) {
    const remainder = value.slice('refs/remotes/'.length);
    const slashIndex = remainder.indexOf('/');
    return slashIndex >= 0 ? remainder.slice(0, slashIndex) : '';
  }
  const slashIndex = value.indexOf('/');
  if (slashIndex <= 0) return '';
  return value.slice(0, slashIndex);
};

export const refreshRemoteTrackingRefs = (remoteName, { gitRunner } = {}) => {
  const remote = String(remoteName || '').trim();
  if (!remote) {
    throw new Error('refreshRemoteTrackingRefs requires a remote name');
  }
  if (typeof gitRunner !== 'function') {
    throw new Error('refreshRemoteTrackingRefs requires gitRunner');
  }
  const result = gitRunner(['fetch', '--prune', remote]);
  if (!result?.ok) {
    throw new Error(`failed to fetch remote ${remote}: ${result?.output || result?.message || 'unknown error'}`);
  }
  return {
    attempted: true,
    ok: true,
    remote,
    output: String(result.output || ''),
  };
};
