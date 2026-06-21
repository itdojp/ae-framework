#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const DEFAULT_PRODUCER_SUMMARY = 'artifacts/agents/producer-normalization-summary.json';
const DEFAULT_ASSURANCE_SUMMARY = 'artifacts/assurance/assurance-summary.json';
const DEFAULT_POLICY_GATE_SUMMARY = 'artifacts/ci/policy-gate-summary.json';
const DEFAULT_BOUNDARY_MAP_SUMMARY = 'artifacts/context-pack/boundary-map-summary.json';
const DEFAULT_CLAIM_EVIDENCE_MANIFEST = 'artifacts/assurance/claim-evidence-manifest.json';
const DEFAULT_VERIFY_LITE_SUMMARY = 'artifacts/verify-lite/verify-lite-run-summary.json';
const DEFAULT_OUTPUT_MD = 'artifacts/review/assurance-review.md';

function usage() {
  process.stdout.write(`Usage: node scripts/assurance/render-pr-review-surface.mjs [options]\n\nOptions:\n  --producer-summary <path>          producer-normalization-summary/v1 input (repeatable; default probe: ${DEFAULT_PRODUCER_SUMMARY})\n  --assurance-summary <path>         assurance-summary/v1 input (default probe: ${DEFAULT_ASSURANCE_SUMMARY})\n  --policy-gate-summary <path>       policy-gate-summary/v1 input (default probe: ${DEFAULT_POLICY_GATE_SUMMARY})\n  --boundary-map-summary <path>      optional boundary-map summary/report input (repeatable; default probe: ${DEFAULT_BOUNDARY_MAP_SUMMARY})\n  --claim-evidence-manifest <path>   optional claim-evidence-manifest/v1 input (repeatable; default probe: ${DEFAULT_CLAIM_EVIDENCE_MANIFEST})\n  --verify-lite-summary <path>       optional verify-lite summary input (default probe: ${DEFAULT_VERIFY_LITE_SUMMARY})\n  --output-md <path>                 output Markdown path (default: ${DEFAULT_OUTPUT_MD})\n  --generated-at <iso-date-time>     override rendered timestamp\n  --title <text>                     Markdown title (default: PR Assurance Review Surface)\n  --help                             show this help\n`);
}

function readRequiredValue(argv, index, flag) {
  const next = argv[index + 1];
  if (!next || next.startsWith('--')) {
    throw new Error(`${flag} requires a value`);
  }
  return next;
}

function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    producerSummaries: [],
    assuranceSummary: DEFAULT_ASSURANCE_SUMMARY,
    policyGateSummary: DEFAULT_POLICY_GATE_SUMMARY,
    boundaryMapSummaries: [],
    claimEvidenceManifests: [],
    verifyLiteSummary: DEFAULT_VERIFY_LITE_SUMMARY,
    outputMd: DEFAULT_OUTPUT_MD,
    generatedAt: null,
    title: 'PR Assurance Review Surface',
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--producer-summary') {
      options.producerSummaries.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--assurance-summary') {
      options.assuranceSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--policy-gate-summary') {
      options.policyGateSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--boundary-map-summary') {
      options.boundaryMapSummaries.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--claim-evidence-manifest') {
      options.claimEvidenceManifests.push(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--verify-lite-summary') {
      options.verifyLiteSummary = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = ensureDateTime(readRequiredValue(argv, index, arg));
      index += 1;
      continue;
    }
    if (arg === '--title') {
      options.title = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  if (options.producerSummaries.length === 0) {
    options.producerSummaries.push(DEFAULT_PRODUCER_SUMMARY);
  }
  if (options.boundaryMapSummaries.length === 0) {
    options.boundaryMapSummaries.push(DEFAULT_BOUNDARY_MAP_SUMMARY);
  }
  if (options.claimEvidenceManifests.length === 0) {
    options.claimEvidenceManifests.push(DEFAULT_CLAIM_EVIDENCE_MANIFEST);
  }
  return options;
}

function ensureDateTime(value) {
  const raw = String(value ?? '').trim();
  if (!Number.isFinite(Date.parse(raw))) {
    throw new Error(`generatedAt must be an ISO date-time: ${raw || '(empty)'}`);
  }
  return new Date(raw).toISOString();
}

function toPosixPath(filePath) {
  return filePath.split(path.sep).join('/');
}

function toDisplayPath(filePath) {
  if (!filePath) return 'not provided';
  const resolved = path.resolve(filePath);
  const relative = path.relative(process.cwd(), resolved);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative)) {
    return toPosixPath(filePath);
  }
  return toPosixPath(relative);
}

function ensureParent(filePath) {
  fs.mkdirSync(path.dirname(path.resolve(filePath)), { recursive: true });
}

function readArtifact(filePath, label, { optional = true } = {}) {
  if (!filePath) {
    return {
      label,
      path: null,
      displayPath: 'not provided',
      status: 'not-provided',
      payload: null,
      error: null,
    };
  }
  const resolved = path.resolve(filePath);
  const displayPath = toDisplayPath(filePath);
  if (!fs.existsSync(resolved)) {
    if (!optional) throw new Error(`${label} not found: ${displayPath}`);
    return {
      label,
      path: resolved,
      displayPath,
      status: 'missing',
      payload: null,
      error: null,
    };
  }
  try {
    return {
      label,
      path: resolved,
      displayPath,
      status: 'present',
      payload: JSON.parse(fs.readFileSync(resolved, 'utf8')),
      error: null,
    };
  } catch (error) {
    if (!optional) throw error;
    return {
      label,
      path: resolved,
      displayPath,
      status: 'invalid-json',
      payload: null,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

function ensureArray(value) {
  return Array.isArray(value) ? value : [];
}

function count(value) {
  return String(Number.isFinite(value) ? value : 0);
}

function text(value, fallback = 'not provided') {
  const raw = value === undefined || value === null ? '' : String(value).trim();
  return raw.length > 0 ? raw : fallback;
}

function listText(values, fallback = 'none') {
  const entries = ensureArray(values).map((value) => text(value, '')).filter(Boolean);
  return entries.length > 0 ? entries.join(', ') : fallback;
}

function escapeMarkdown(value) {
  return text(value, '')
    .replaceAll('\\', '\\\\')
    .replaceAll('|', '\\|')
    .replaceAll('\n', '<br>');
}

function renderTable(headers, rows) {
  const safeRows = rows.length > 0 ? rows : [headers.map(() => 'not provided')];
  return [
    `| ${headers.map(escapeMarkdown).join(' | ')} |`,
    `| ${headers.map(() => '---').join(' | ')} |`,
    ...safeRows.map((row) => `| ${row.map(escapeMarkdown).join(' | ')} |`),
  ].join('\n');
}

function firstPresent(artifacts) {
  return artifacts.find((artifact) => artifact.status === 'present') ?? null;
}

function summarizeInputs(options) {
  const producerArtifacts = options.producerSummaries.map((inputPath) =>
    readArtifact(inputPath, 'producer-normalization-summary'),
  );
  const boundaryArtifacts = options.boundaryMapSummaries.map((inputPath) =>
    readArtifact(inputPath, 'boundary-map-summary'),
  );
  const manifestArtifacts = options.claimEvidenceManifests.map((inputPath) =>
    readArtifact(inputPath, 'claim-evidence-manifest'),
  );
  return {
    producerArtifacts,
    assuranceArtifact: readArtifact(options.assuranceSummary, 'assurance-summary'),
    policyArtifact: readArtifact(options.policyGateSummary, 'policy-gate-summary'),
    boundaryArtifacts,
    manifestArtifacts,
    verifyLiteArtifact: readArtifact(options.verifyLiteSummary, 'verify-lite-run-summary'),
  };
}

function collectGeneratedAt(options, artifacts) {
  if (options.generatedAt) return options.generatedAt;
  const candidates = [
    artifacts.assuranceArtifact.payload?.generatedAt,
    artifacts.policyArtifact.payload?.generatedAtUtc,
    firstPresent(artifacts.producerArtifacts)?.payload?.generatedAt,
    firstPresent(artifacts.manifestArtifacts)?.payload?.generatedAt,
    firstPresent(artifacts.boundaryArtifacts)?.payload?.generatedAt,
    artifacts.verifyLiteArtifact.payload?.timestamp,
  ];
  const candidate = candidates.find((value) => Number.isFinite(Date.parse(String(value ?? ''))));
  return candidate ? new Date(candidate).toISOString() : new Date().toISOString();
}

function artifactRows(artifacts) {
  return [
    ...artifacts.producerArtifacts,
    artifacts.assuranceArtifact,
    artifacts.policyArtifact,
    ...artifacts.boundaryArtifacts,
    ...artifacts.manifestArtifacts,
    artifacts.verifyLiteArtifact,
  ].map((artifact) => [
    artifact.label,
    artifact.displayPath,
    artifact.error ? `${artifact.status}: ${artifact.error}` : artifact.status,
  ]);
}

function producerRows(producerArtifacts) {
  return producerArtifacts.map((artifact) => {
    const payload = artifact.payload ?? {};
    const summary = payload.summary ?? {};
    const producer = payload.producer ?? {};
    const judgment = payload.controlPlaneJudgment ?? {};
    return [
      artifact.displayPath,
      text(producer.displayName ?? producer.id),
      text(producer.category),
      count(summary.rawSignals),
      count(summary.changedFiles),
      count(summary.commands),
      count(summary.missingEvidence),
      count(summary.reportOnlyFindings),
      text(judgment.result ?? (judgment.emitsDecision === false ? 'not-emitted' : null)),
    ];
  });
}

function changedFileRows(producerArtifacts, policyArtifact) {
  const rows = [];
  for (const artifact of producerArtifacts) {
    const changedFiles = ensureArray(artifact.payload?.producerAssertions?.changedFiles);
    for (const entry of changedFiles) {
      rows.push([
        text(entry.path),
        text(entry.role),
        text(entry.expectedArtifact),
      ]);
    }
  }
  if (rows.length === 0) {
    for (const filePath of ensureArray(policyArtifact.payload?.changedFiles)) {
      rows.push([filePath, 'policy changedFiles', 'policy-gate-summary/v1']);
    }
  }
  return rows.slice(0, 12);
}

function boundaryRows(boundaryArtifacts, assuranceSummary) {
  const rows = boundaryArtifacts.map((artifact) => {
    const payload = artifact.payload ?? {};
    return [
      artifact.displayPath,
      text(payload.status, artifact.status),
      text(payload.reviewStatus),
      count(payload.counts?.totalFindings),
      text(payload.evidenceKind),
      text(payload.defaultDecision),
      text(payload.interpretation ?? payload.statusReason),
    ];
  });
  if (rows.some((row) => row[1] !== 'missing' && row[1] !== 'not-provided')) return rows;
  const boundaryMap = assuranceSummary?.reviewSurface?.boundaryMap;
  if (!boundaryMap) return rows;
  return [[
    listText(boundaryMap.artifactPaths),
    text(boundaryMap.status),
    listText(boundaryMap.reviewStatuses),
    count(boundaryMap.totalFindings),
    text(boundaryMap.evidenceKind),
    'from assurance-summary reviewSurface',
    text(boundaryMap.interpretation),
  ]];
}

function findManifestClaim(manifestArtifacts, claimId) {
  for (const artifact of manifestArtifacts) {
    const match = ensureArray(artifact.payload?.claims).find((claim) => claim.id === claimId);
    if (match) return match;
  }
  return null;
}

function evidenceKindsFromClaim(claim, manifestClaim) {
  return listText([
    ...ensureArray(claim?.observedEvidenceKinds),
    ...ensureArray(manifestClaim?.evidenceRefs).map((entry) => entry.kind),
  ]);
}

function claimRows(assuranceSummary, manifestArtifacts) {
  const claims = ensureArray(assuranceSummary?.claims);
  const rows = claims.map((claim) => {
    const manifestClaim = findManifestClaim(manifestArtifacts, claim.claimId);
    return [
      text(claim.claimId),
      text(claim.status),
      text(manifestClaim?.status),
      evidenceKindsFromClaim(claim, manifestClaim),
      listText(claim.missingLanes),
      listText(claim.missingEvidenceKinds),
      count(ensureArray(manifestClaim?.missingEvidenceRefs).length),
      count(ensureArray(manifestClaim?.waiverRefs).length),
      count(ensureArray(manifestClaim?.runtimeControls).length),
    ];
  });

  if (rows.length > 0) return rows;
  for (const artifact of manifestArtifacts) {
    for (const claim of ensureArray(artifact.payload?.claims)) {
      rows.push([
        text(claim.id),
        'not provided',
        text(claim.status),
        listText(ensureArray(claim.evidenceRefs).map((entry) => entry.kind)),
        'not provided',
        'not provided',
        count(ensureArray(claim.missingEvidenceRefs).length),
        count(ensureArray(claim.waiverRefs).length),
        count(ensureArray(claim.runtimeControls).length),
      ]);
    }
  }
  return rows;
}

function missingEvidenceRows(artifacts) {
  const rows = [];
  for (const artifact of artifacts.producerArtifacts) {
    for (const entry of ensureArray(artifact.payload?.controlPlaneRouting?.missingEvidence)) {
      rows.push([
        'producer-summary',
        artifact.displayPath,
        text(entry.claimId ?? entry.command ?? entry.kind),
        text(entry.summary),
      ]);
    }
  }
  for (const claim of ensureArray(artifacts.assuranceArtifact.payload?.claims)) {
    if (
      claim.status !== 'satisfied' ||
      ensureArray(claim.missingLanes).length > 0 ||
      ensureArray(claim.missingEvidenceKinds).length > 0 ||
      ensureArray(claim.independenceWarnings).length > 0
    ) {
      rows.push([
        'assurance-summary',
        artifacts.assuranceArtifact.displayPath,
        text(claim.claimId),
        `status=${text(claim.status)}; missingLanes=${listText(claim.missingLanes)}; missingEvidenceKinds=${listText(claim.missingEvidenceKinds)}; warnings=${listText(claim.independenceWarnings)}`,
      ]);
    }
  }
  for (const artifact of artifacts.manifestArtifacts) {
    for (const claim of ensureArray(artifact.payload?.claims)) {
      const missingRefs = ensureArray(claim.missingEvidenceRefs);
      if (claim.status === 'unresolved' || claim.status === 'partial' || claim.status === 'failed' || missingRefs.length > 0) {
        rows.push([
          'claim-evidence-manifest',
          artifact.displayPath,
          text(claim.id),
          `status=${text(claim.status)}; missingEvidenceRefs=${listText(missingRefs.map((entry) => entry.id ?? entry.reason))}`,
        ]);
      }
    }
  }
  return rows.slice(0, 20);
}

function waiverRows(manifestArtifacts, assuranceSummary) {
  const rows = [];
  for (const artifact of manifestArtifacts) {
    for (const claim of ensureArray(artifact.payload?.claims)) {
      for (const waiver of ensureArray(claim.waiverRefs)) {
        rows.push([
          text(claim.id),
          text(waiver.id),
          text(waiver.status),
          text(waiver.owner),
          text(waiver.expires),
          artifact.displayPath,
        ]);
      }
      for (const control of ensureArray(claim.runtimeControls)) {
        rows.push([
          text(claim.id),
          text(control.id ?? control.kind, 'runtime-control'),
          text(control.status ?? 'runtime-mitigated'),
          text(control.owner),
          text(control.expires),
          artifact.displayPath,
        ]);
      }
    }
  }
  for (const waiver of ensureArray(assuranceSummary?.reviewSurface?.waivers?.waiverRefs)) {
    rows.push([
      text(waiver.claimId),
      text(waiver.id),
      text(waiver.status),
      text(waiver.owner),
      text(waiver.expires),
      text(waiver.source),
    ]);
  }
  return rows;
}

function policyRows(policyArtifact, assuranceSummary) {
  const policy = policyArtifact.payload ?? {};
  const evaluation = policy.evaluation ?? {};
  const assurance = evaluation.assurance ?? {};
  const fallbackPolicy = assuranceSummary?.reviewSurface?.policyDecision ?? {};
  return [[
    policyArtifact.displayPath,
    text(evaluation.selectedRiskLabel),
    text(assurance.mode ?? fallbackPolicy.mode),
    text(assurance.result ?? fallbackPolicy.result),
    text(evaluation.ok ?? fallbackPolicy.ok),
    count(ensureArray(evaluation.errors).length + ensureArray(assurance.errors).length),
    count(ensureArray(evaluation.warnings).length + ensureArray(assurance.warnings).length),
  ]];
}

function reviewerActions(artifacts) {
  const assuranceSummary = artifacts.assuranceArtifact.payload;
  const reviewSurface = assuranceSummary?.reviewSurface;
  const actions = [
    `Start with this Markdown before raw logs; then open \`${artifacts.assuranceArtifact.displayPath}\` and \`${artifacts.policyArtifact.displayPath}\`.`,
    'Treat producer assertions as evidence input only; do not treat producer conclusion as approval.',
  ];
  if (reviewSurface?.recommendedReviewerAction?.action) {
    actions.push(`Follow recommendedReviewerAction=\`${reviewSurface.recommendedReviewerAction.action}\`: ${reviewSurface.recommendedReviewerAction.reason}`);
  }
  if (missingEvidenceRows(artifacts).length > 0) {
    actions.push('Resolve or explicitly accept the listed missing evidence / unresolved claim rows before using the surface as release evidence.');
  }
  if (artifacts.boundaryArtifacts.some((artifact) => artifact.status !== 'present')) {
    actions.push('Boundary artifact is missing or not provided; record why scope drift is not assessed, or generate the Boundary Map summary.');
  }
  if (artifacts.manifestArtifacts.some((artifact) => artifact.status !== 'present')) {
    actions.push('Claim evidence manifest is missing or not provided; do not infer claim-level satisfied/waived status from absence.');
  }
  const policyResult = artifacts.policyArtifact.payload?.evaluation?.assurance?.result;
  const policyMode = artifacts.policyArtifact.payload?.evaluation?.assurance?.mode;
  actions.push(`For ordinary PRs, report-only findings remain reviewer context; for risk/high-assurance PRs, follow policy decision result=\`${text(policyResult)}\` mode=\`${text(policyMode)}\`.`);
  return actions;
}

export function renderPrReviewSurfaceMarkdown({ options, artifacts, generatedAt }) {
  const assuranceSummary = artifacts.assuranceArtifact.payload;
  const rows = {
    artifacts: artifactRows(artifacts),
    producers: producerRows(artifacts.producerArtifacts),
    changedFiles: changedFileRows(artifacts.producerArtifacts, artifacts.policyArtifact),
    boundaries: boundaryRows(artifacts.boundaryArtifacts, assuranceSummary),
    claims: claimRows(assuranceSummary, artifacts.manifestArtifacts),
    missingEvidence: missingEvidenceRows(artifacts),
    waivers: waiverRows(artifacts.manifestArtifacts, assuranceSummary),
    policies: policyRows(artifacts.policyArtifact, assuranceSummary),
  };

  return [
    `# ${options.title}`,
    '',
    '> Reviewer-first Markdown generated from schema-backed assurance artifacts. It summarizes evidence and gaps; it does not approve, prove, or merge a PR.',
    '',
    `- generatedAt: \`${generatedAt}\``,
    `- recommendedReviewerAction: \`${text(assuranceSummary?.reviewSurface?.recommendedReviewerAction?.action, 'not provided')}\``,
    `- reason: ${text(assuranceSummary?.reviewSurface?.recommendedReviewerAction?.reason, 'not provided')}`,
    '',
    '## Artifact inputs',
    '',
    renderTable(['artifact', 'path', 'status'], rows.artifacts),
    '',
    '## Producer / task scope',
    '',
    'Producer output is displayed as report-only input. It is never rendered as approval.',
    '',
    renderTable(
      ['artifact', 'producer', 'category', 'raw signals', 'changed files', 'commands', 'missing evidence', 'report-only findings', 'control-plane judgment'],
      rows.producers,
    ),
    '',
    '### Changed-file scope',
    '',
    renderTable(['path', 'role', 'expected artifact'], rows.changedFiles),
    '',
    '## Boundary / scope status',
    '',
    'A missing boundary artifact is shown as `missing` / `not provided`; absence is not rendered as boundary-ok.',
    '',
    renderTable(['artifact', 'status', 'review status', 'findings', 'evidence kind', 'decision', 'interpretation'], rows.boundaries),
    '',
    '## Claims and evidence status',
    '',
    '`tested`, `model-checked`, `proved`, `waived`, `unresolved`, and `runtime-mitigated` remain separate artifact states. This renderer shows source artifact status and evidence kinds without collapsing them into approval.',
    '',
    renderTable(
      ['claim', 'assurance status', 'manifest status', 'evidence kinds', 'missing lanes', 'missing evidence kinds', 'missing evidence refs', 'waiver refs', 'runtime controls'],
      rows.claims,
    ),
    '',
    '## Missing evidence / unresolved claims',
    '',
    renderTable(['source', 'artifact', 'claim or evidence', 'review note'], rows.missingEvidence),
    '',
    '## Waivers / runtime controls',
    '',
    'Waived and runtime-mitigated claims require explicit reviewer attention; they are not counted as satisfied proof.',
    '',
    renderTable(['claim', 'waiver/control', 'status', 'owner', 'expires', 'source'], rows.waivers),
    '',
    '## Policy decision / report-only vs blocking',
    '',
    renderTable(['artifact', 'risk label', 'assurance mode', 'assurance result', 'ok', 'errors', 'warnings'], rows.policies),
    '',
    '## Reviewer action list',
    '',
    ...reviewerActions(artifacts).map((action) => `- ${action}`),
    '',
    '## Interpretation guardrails',
    '',
    '- Producer conclusion is not approval.',
    '- Green baseline checks are not proof for high-assurance claims.',
    '- Missing optional artifacts must stay visible as `missing` / `not provided`.',
    '- Policy escalation depends on risk labels, assurance profile, and selected critical claims, not on the agent vendor.',
    '',
  ].join('\n');
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    usage();
    return 0;
  }
  const artifacts = summarizeInputs(options);
  const generatedAt = collectGeneratedAt(options, artifacts);
  const markdown = renderPrReviewSurfaceMarkdown({ options, artifacts, generatedAt });
  ensureParent(options.outputMd);
  fs.writeFileSync(options.outputMd, markdown, 'utf8');
  process.stdout.write(`[assurance-review-surface] wrote ${toDisplayPath(options.outputMd)}\n`);
  return 0;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    process.exitCode = run();
  } catch (error) {
    process.stderr.write(`[assurance-review-surface] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
