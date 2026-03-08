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

export const deriveFetchRemotes = (remoteName, baseRef) => {
  const remotes = [];
  const primaryRemote = String(remoteName || '').trim();
  const baseRemote = deriveRemoteFromBaseRef(baseRef);
  if (primaryRemote) remotes.push(primaryRemote);
  if (baseRemote && !remotes.includes(baseRemote)) remotes.push(baseRemote);
  return remotes;
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
    const detail = String(result?.output || result?.message || 'unknown error').trim();
    return {
      attempted: true,
      ok: false,
      remote,
      output: String(result?.output || ''),
      message: `failed to fetch remote ${remote}: ${detail || 'unknown error'}`,
    };
  }
  return {
    attempted: true,
    ok: true,
    remote,
    output: String(result.output || ''),
    message: '',
  };
};

export const refreshRemoteTrackingRefsBatch = (remoteNames, { gitRunner } = {}) => {
  const remotes = Array.from(
    new Set(
      []
        .concat(remoteNames || [])
        .map((value) => String(value || '').trim())
        .filter(Boolean),
    ),
  );
  if (remotes.length === 0) {
    throw new Error('refreshRemoteTrackingRefsBatch requires at least one remote name');
  }
  const details = remotes.map((remote) => refreshRemoteTrackingRefs(remote, { gitRunner }));
  const failed = details.find((detail) => !detail.ok);
  return {
    attempted: true,
    ok: !failed,
    remote: remotes.join(','),
    remotes,
    output: details
      .map((detail) => String(detail.output || '').trim())
      .filter(Boolean)
      .join('\n'),
    message: failed ? String(failed.message || '') : '',
    details,
  };
};
