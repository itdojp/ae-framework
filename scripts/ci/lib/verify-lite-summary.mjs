export const renderVerifyLiteSummary = (summary, options = {}) => {
  if (!summary || typeof summary !== 'object') {
    throw new Error('Invalid summary payload');
  }

  const {
    schemaVersion,
    timestamp,
    flags = {},
    steps = {},
    traceability = null,
    discoveryPack = null,
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
    if (normalized === 'warn') return '⚠️ warn';
    if (normalized === 'pass') return '✅ pass';
    if (normalized === 'fail') return '❌ fail';
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
    ...(traceability && typeof traceability === 'object'
      ? [`- traceability missing count: ${Number.isFinite(traceability.missingCount) ? traceability.missingCount : 'n/a'} (${formatStatus(traceability.status)})`]
      : []),
  ];

  const orderedKeys = [
    'install',
    'specCompilerBuild',
    'typeCheck',
    'reasonCodeRegistryValidation',
    'lint',
    'build',
    'stateMachineValidation',
    'stateMachineRender',
    'contextPackValidation',
    'contextPackFunctorValidation',
    'contextPackNaturalTransformationValidation',
    'contextPackProductCoproductValidation',
    'contextPackPhase5Validation',
    'discoveryPackValidation',
    'discoveryPackCompile',
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
  const discoveryLines = [];
  if (discoveryPack && typeof discoveryPack === 'object') {
    discoveryLines.push('', 'Discovery Pack:');
    discoveryLines.push(`- mode: \`${discoveryPack.mode ?? 'report-only'}\``);
    discoveryLines.push(`- reason: ${discoveryPack.reason ? `\`${escapeHtml(discoveryPack.reason)}\`` : 'n/a'}`);
    discoveryLines.push(`- source present: ${yesNo(Boolean(discoveryPack.sourcePresent))}`);
    discoveryLines.push(`- validate: ${formatStatus(discoveryPack.validateStatus)}`);
    discoveryLines.push(`- compile: ${formatStatus(discoveryPack.compileStatus)}`);
    discoveryLines.push(`- strict approved: ${yesNo(Boolean(discoveryPack.strictApproved))}`);
    discoveryLines.push(`- fail-on: ${Array.isArray(discoveryPack.failOn) && discoveryPack.failOn.length > 0 ? discoveryPack.failOn.map((entry) => `\`${escapeHtml(entry)}\``).join(', ') : 'n/a'}`);
    discoveryLines.push(`- scanned/warn/fail files: ${discoveryPack.scannedFiles ?? 0}/${discoveryPack.warningFiles ?? 0}/${discoveryPack.failedFiles ?? 0}`);
    discoveryLines.push(`- blocking open questions: ${discoveryPack.blockingOpenQuestions ?? 0}`);
    discoveryLines.push(`- orphan approved requirements: ${discoveryPack.orphanApprovedRequirements ?? 0}`);
    discoveryLines.push(`- orphan approved business use cases: ${discoveryPack.orphanApprovedBusinessUseCases ?? 0}`);
    discoveryLines.push(`- compile selected/excluded/skipped: ${discoveryPack.compileSelectedCount ?? 0}/${discoveryPack.compileExcludedByStatusCount ?? 0}/${discoveryPack.compileSkippedByTargetCount ?? 0}`);
  }
  if (Object.keys(artifacts).length > 0) {
    const { artifactsUrl } = options;
    const labelMap = {
      lintSummary: 'Lint Baseline Diff',
      lintLog: 'Lint Log',
      mutationSummary: 'Mutation Summary JSON',
      mutationSurvivors: 'Mutation Survivors JSON',
      contextPackReportJson: 'Context Pack Validation JSON',
      contextPackReportMarkdown: 'Context Pack Validation Markdown',
      contextPackFunctorReportJson: 'Context Pack Functor JSON',
      contextPackFunctorReportMarkdown: 'Context Pack Functor Markdown',
      contextPackNaturalTransformationReportJson: 'Context Pack Natural Transformation JSON',
      contextPackNaturalTransformationReportMarkdown: 'Context Pack Natural Transformation Markdown',
      contextPackProductCoproductReportJson: 'Context Pack Product/Coproduct JSON',
      contextPackProductCoproductReportMarkdown: 'Context Pack Product/Coproduct Markdown',
      contextPackPhase5ReportJson: 'Context Pack Phase5 Templates JSON',
      contextPackPhase5ReportMarkdown: 'Context Pack Phase5 Templates Markdown',
      discoveryPackValidateReportJson: 'Discovery Pack Validation JSON',
      discoveryPackValidateReportMarkdown: 'Discovery Pack Validation Markdown',
      discoveryPackCompileReportJson: 'Discovery Pack Compile JSON',
      discoveryPackCompileReportMarkdown: 'Discovery Pack Compile Markdown',
      discoveryPackPlanSpec: 'Discovery Pack Plan-Spec Markdown',
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
      'contextPackReportJson',
      'contextPackReportMarkdown',
      'contextPackFunctorReportJson',
      'contextPackFunctorReportMarkdown',
      'contextPackNaturalTransformationReportJson',
      'contextPackNaturalTransformationReportMarkdown',
      'contextPackProductCoproductReportJson',
      'contextPackProductCoproductReportMarkdown',
      'contextPackPhase5ReportJson',
      'contextPackPhase5ReportMarkdown',
      'discoveryPackValidateReportJson',
      'discoveryPackValidateReportMarkdown',
      'discoveryPackCompileReportJson',
      'discoveryPackCompileReportMarkdown',
      'discoveryPackPlanSpec',
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
    ...discoveryLines,
    '',
    ...artifactLines,
  ];

  return output.join('\n');
};
