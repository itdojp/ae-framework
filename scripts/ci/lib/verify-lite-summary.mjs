export const renderVerifyLiteSummary = (summary, options = {}) => {
  if (!summary || typeof summary !== 'object') {
    throw new Error('Invalid summary payload');
  }

  const {
    schemaVersion,
    timestamp,
    flags = {},
    steps = {},
    artifacts = {}
  } = summary;

  const yesNo = (value) => (value ? '✅' : '❌');
  const escapeHtml = (text) =>
    String(text).replace(/[&<>'"]/g, (char) => {
      switch (char) {
        case '&':
          return '&amp;';
        case '<':
          return '&lt;';
        case '>':
          return '&gt;';
        case '"':
          return '&quot;';
        case "'":
          return '&#39;';
        default:
          return char;
      }
    });

  const formatStatus = (status) => {
    if (!status) return 'n/a';
    const normalized = String(status).toLowerCase();
    if (normalized === 'success') return '✅ success';
    if (normalized === 'failure') return '❌ failure';
    if (normalized === 'skipped') return '⏭️ skipped';
    if (normalized === 'pending') return '… pending';
    return normalized;
  };

  const flagLines = [
    `- install flags: \`${flags.install ?? ''}\``,
    `- no frozen lockfile: ${yesNo(Boolean(flags.noFrozen))}`,
    `- keep lint log: ${yesNo(Boolean(flags.keepLintLog))}`,
    `- enforce lint: ${yesNo(Boolean(flags.enforceLint))}`,
    `- run mutation: ${yesNo(Boolean(flags.runMutation))}`,
  ];

  const orderedKeys = [
    'install',
    'specCompilerBuild',
    'typeCheck',
    'lint',
    'build',
    'bddLint',
    'mutationQuick',
    'conformanceReport',
  ];

  const seen = new Set();
  const orderedSteps = [];

  for (const key of orderedKeys) {
    if (steps[key]) {
      orderedSteps.push([key, steps[key]]);
      seen.add(key);
    }
  }

  for (const [key, value] of Object.entries(steps)) {
    if (!seen.has(key)) {
      orderedSteps.push([key, value]);
    }
  }

  const titleCase = (name) =>
    name
      .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
      .replace(/[-_]/g, ' ')
      .replace(/\b\w/g, (ch) => ch.toUpperCase());

  const tableLines = [
    '| Step | Status | Notes |',
    '| --- | --- | --- |',
  ];

  for (const [key, value] of orderedSteps) {
    const status = formatStatus(value?.status);
    const notes = value?.notes ? escapeHtml(value.notes).replace(/\n/g, '<br>') : '';
    tableLines.push(`| ${titleCase(key)} | ${status} | ${notes} |`);
  }

  const artifactLines = [];
  if (Object.keys(artifacts).length > 0) {
    const { artifactsUrl } = options;
    const labelMap = {
      lintSummary: 'Lint Baseline Diff',
      lintLog: 'Lint Log',
      mutationSummary: 'Mutation Summary JSON',
      mutationSurvivors: 'Mutation Survivors JSON',
      conformanceSummary: 'Conformance Summary JSON',
      conformanceSummaryMarkdown: 'Conformance Summary Markdown',
    };
    const formatArtifact = (value) => {
      if (!value) return 'n/a';
      if (/^https?:\/\//i.test(value)) {
        return `[Data Link](${value})`;
      }
      if (artifactsUrl) {
        return `\`${value}\` ([Data Link](${artifactsUrl}))`;
      }
      return `\`${value}\``;
    };

    artifactLines.push('\nArtifacts:');
    const preferredOrder = [
      'lintSummary',
      'lintLog',
      'mutationSummary',
      'mutationSurvivors',
      'conformanceSummary',
      'conformanceSummaryMarkdown',
    ];
    const handled = new Set();
    for (const key of preferredOrder) {
      if (!Object.prototype.hasOwnProperty.call(artifacts, key)) continue;
      handled.add(key);
      artifactLines.push(`- ${labelMap[key] ?? key}: ${formatArtifact(artifacts[key])}`);
    }
    for (const [key, value] of Object.entries(artifacts)) {
      if (handled.has(key)) continue;
      artifactLines.push(`- ${key}: ${formatArtifact(value)}`);
    }
    if (artifactsUrl) {
      artifactLines.push(`- GitHub Artifacts: [Open](${artifactsUrl})`);
    }
  }

  const output = [
    timestamp ? `Timestamp: ${timestamp}` : 'Timestamp: n/a',
    `Schema Version: ${schemaVersion ?? 'unknown'}`,
    ...flagLines,
    '',
    ...tableLines,
    '',
    ...artifactLines,
  ];

  return output.join('\n');
};
