#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_INPUT_PATH = 'artifacts/change-package/change-package.json';
const DEFAULT_SCHEMA_PATH = 'schema/change-package.schema.json';
const DEFAULT_V2_SCHEMA_PATH = 'schema/change-package-v2.schema.json';
const DEFAULT_OUTPUT_JSON_PATH = 'artifacts/change-package/change-package-validation.json';
const DEFAULT_OUTPUT_MD_PATH = 'artifacts/change-package/change-package-validation.md';
const DEFAULT_ARTIFACT_ROOT = '.';

function splitCommaValues(raw) {
  if (!raw) return [];
  return raw
    .split(',')
    .map((entry) => String(entry || '').trim())
    .filter(Boolean);
}

function toUnique(values) {
  return [...new Set(values)];
}

function parseArgs(argv = process.argv) {
  const options = {
    inputPath: DEFAULT_INPUT_PATH,
    schemaPath: DEFAULT_SCHEMA_PATH,
    outputJsonPath: DEFAULT_OUTPUT_JSON_PATH,
    outputMarkdownPath: DEFAULT_OUTPUT_MD_PATH,
    artifactRoot: '',
    artifactRootExplicit: false,
    policyDecisionPath: '',
    strict: false,
    requiredEvidenceIds: [],
    help: false,
    schemaPathExplicit: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    const readValue = (name) => {
      if (!next || next.startsWith('-')) {
        throw new Error(`missing value for ${name}`);
      }
      index += 1;
      return next;
    };

    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--file' || arg === '--input') {
      options.inputPath = readValue(arg);
      continue;
    }
    if (arg.startsWith('--file=')) {
      options.inputPath = arg.slice('--file='.length);
      continue;
    }
    if (arg.startsWith('--input=')) {
      options.inputPath = arg.slice('--input='.length);
      continue;
    }
    if (arg === '--schema') {
      options.schemaPath = readValue('--schema');
      options.schemaPathExplicit = true;
      continue;
    }
    if (arg.startsWith('--schema=')) {
      options.schemaPath = arg.slice('--schema='.length);
      options.schemaPathExplicit = true;
      continue;
    }
    if (arg === '--artifact-root') {
      options.artifactRoot = readValue('--artifact-root');
      options.artifactRootExplicit = true;
      continue;
    }
    if (arg.startsWith('--artifact-root=')) {
      options.artifactRoot = arg.slice('--artifact-root='.length);
      options.artifactRootExplicit = true;
      continue;
    }
    if (arg === '--policy-decision') {
      options.policyDecisionPath = readValue('--policy-decision');
      continue;
    }
    if (arg.startsWith('--policy-decision=')) {
      options.policyDecisionPath = arg.slice('--policy-decision='.length);
      continue;
    }
    if (arg === '--output-json') {
      options.outputJsonPath = readValue('--output-json');
      continue;
    }
    if (arg.startsWith('--output-json=')) {
      options.outputJsonPath = arg.slice('--output-json='.length);
      continue;
    }
    if (arg === '--output-md') {
      options.outputMarkdownPath = readValue('--output-md');
      continue;
    }
    if (arg.startsWith('--output-md=')) {
      options.outputMarkdownPath = arg.slice('--output-md='.length);
      continue;
    }
    if (arg === '--required-evidence') {
      options.requiredEvidenceIds.push(...splitCommaValues(readValue('--required-evidence')));
      continue;
    }
    if (arg.startsWith('--required-evidence=')) {
      options.requiredEvidenceIds.push(...splitCommaValues(arg.slice('--required-evidence='.length)));
      continue;
    }
    if (arg === '--strict') {
      options.strict = true;
      continue;
    }
    if (arg === '--no-strict') {
      options.strict = false;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  const envRequiredEvidence = splitCommaValues(process.env.AE_CHANGE_PACKAGE_REQUIRED_EVIDENCE || '');
  if (options.requiredEvidenceIds.length === 0 && envRequiredEvidence.length > 0) {
    options.requiredEvidenceIds = envRequiredEvidence;
  }

  options.requiredEvidenceIds = toUnique(options.requiredEvidenceIds);
  return options;
}

function printHelp() {
  process.stdout.write(
    `Change Package validator\n\n`
    + `Usage:\n`
    + `  node scripts/change-package/validate.mjs [options]\n\n`
    + `Options:\n`
    + `  --file <path>                 input Change Package JSON (default: ${DEFAULT_INPUT_PATH})\n`
    + `  --schema <path>               JSON Schema path (default: ${DEFAULT_SCHEMA_PATH}; v2 auto-detected)\n`
    + `  --output-json <path>          output JSON report (default: ${DEFAULT_OUTPUT_JSON_PATH})\n`
    + `  --output-md <path>            output Markdown report (default: ${DEFAULT_OUTPUT_MD_PATH})\n`
    + `  --artifact-root <path>        root for v2 artifactRefs existence checks (default: payload evidence.artifactRoot, then ${DEFAULT_ARTIFACT_ROOT})\n`
    + `  --policy-decision <path>      optional policy-decision/v1 for v2 status consistency checks\n`
    + `  --required-evidence <ids>     comma-separated evidence IDs to require\n`
    + `  --strict                      fail on missing required evidence\n`
    + `  --help, -h                    show help\n`,
  );
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function readJsonFile(filePath) {
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`file not found: ${resolved}`);
  }
  return JSON.parse(fs.readFileSync(resolved, 'utf8'));
}

function readJsonOptional(filePath) {
  if (!filePath) return null;
  const resolved = path.resolve(filePath);
  if (!fs.existsSync(resolved)) return null;
  return JSON.parse(fs.readFileSync(resolved, 'utf8'));
}

function validateSchema(schema, payload) {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const ok = validate(payload);
  return {
    ok,
    errors: validate.errors || [],
  };
}

function inferHighRisk(payload) {
  const risk = payload?.risk || {};
  if (risk?.selected === 'risk:high' || risk?.inferred === 'risk:high') {
    return true;
  }
  return Boolean(risk?.isHighRisk);
}

function resolveRequiredEvidenceIds(options, payload) {
  if (options.requiredEvidenceIds.length > 0) {
    return options.requiredEvidenceIds;
  }
  const highRisk = inferHighRisk(payload);
  return highRisk
    ? ['verifyLiteSummary', 'policyGateSummary', 'harnessHealth']
    : ['verifyLiteSummary'];
}

function evaluateEvidence(payload, requiredEvidenceIds) {
  const items = Array.isArray(payload?.evidence?.items) ? payload.evidence.items : [];
  const itemMap = new Map();
  for (const item of items) {
    const id = String(item?.id || '').trim();
    if (!id) continue;
    itemMap.set(id, item);
  }

  const missingRequiredEvidence = requiredEvidenceIds
    .map((id) => {
      const item = itemMap.get(id);
      const present = Boolean(item?.present);
      if (present) return null;
      return {
        id,
        present: false,
        reason: item ? 'present=false' : 'missing-item',
      };
    })
    .filter(Boolean);

  const presentCountActual = items.filter((item) => item?.present === true).length;
  const missingCountActual = items.length - presentCountActual;
  const presentCountDeclared = Number(payload?.evidence?.presentCount);
  const missingCountDeclared = Number(payload?.evidence?.missingCount);

  const countMismatches = [];
  if (Number.isFinite(presentCountDeclared) && presentCountDeclared !== presentCountActual) {
    countMismatches.push(
      `presentCount mismatch: declared=${presentCountDeclared}, actual=${presentCountActual}`,
    );
  }
  if (Number.isFinite(missingCountDeclared) && missingCountDeclared !== missingCountActual) {
    countMismatches.push(
      `missingCount mismatch: declared=${missingCountDeclared}, actual=${missingCountActual}`,
    );
  }

  return {
    requiredEvidenceIds,
    missingRequiredEvidence,
    countMismatches,
    presentCountActual,
    missingCountActual,
    itemCount: items.length,
  };
}

function isChangePackageV2(payload) {
  return payload?.schemaVersion === 'change-package/v2';
}

function resolveSchemaPath(options, payload) {
  if (!options.schemaPathExplicit && isChangePackageV2(payload)) {
    return DEFAULT_V2_SCHEMA_PATH;
  }
  return options.schemaPath;
}

function ensureArray(value) {
  return Array.isArray(value) ? value : [];
}

function normalizeRefForFs(artifactRef) {
  const raw = String(artifactRef || '').trim();
  if (!raw) {
    return '';
  }
  if (path.win32.isAbsolute(raw)) return raw.split('#')[0].trim();
  if (/^[a-z][a-z0-9+.-]*:/iu.test(raw)) return '';
  return raw.split('#')[0].trim();
}

function artifactExists(artifactRoot, artifactRef) {
  const normalized = normalizeRefForFs(artifactRef);
  if (!normalized) return true;
  const candidate = path.isAbsolute(normalized) || path.win32.isAbsolute(normalized)
    ? normalized
    : path.resolve(artifactRoot || DEFAULT_ARTIFACT_ROOT, normalized);
  return fs.existsSync(candidate);
}

function resolveArtifactRoot(options, payload) {
  if (options.artifactRootExplicit) {
    return path.resolve(options.artifactRoot || DEFAULT_ARTIFACT_ROOT);
  }
  return path.resolve(payload?.evidence?.artifactRoot || DEFAULT_ARTIFACT_ROOT);
}

function collectArtifactRefs(payload) {
  const refs = [];
  for (const [index, claim] of ensureArray(payload?.claims).entries()) {
    for (const artifactRef of ensureArray(claim?.artifactRefs)) {
      refs.push({ path: `/claims/${index}/artifactRefs`, artifactRef });
    }
  }
  for (const [index, assumption] of ensureArray(payload?.assumptions).entries()) {
    for (const artifactRef of ensureArray(assumption?.evidenceRefs)) {
      refs.push({ path: `/assumptions/${index}/evidenceRefs`, artifactRef });
    }
  }
  for (const [index, waiver] of ensureArray(payload?.waivers).entries()) {
    for (const artifactRef of ensureArray(waiver?.evidenceRefs)) {
      refs.push({ path: `/waivers/${index}/evidenceRefs`, artifactRef });
    }
  }
  for (const [index, obligation] of ensureArray(payload?.proofObligations).entries()) {
    for (const artifactRef of ensureArray(obligation?.artifactRefs)) {
      refs.push({ path: `/proofObligations/${index}/artifactRefs`, artifactRef });
    }
  }
  for (const [index, counterexample] of ensureArray(payload?.counterexamples).entries()) {
    if (counterexample?.artifactPath) {
      refs.push({ path: `/counterexamples/${index}/artifactPath`, artifactRef: counterexample.artifactPath });
    }
  }
  return refs;
}

function buildClaimIdSet(payload) {
  return new Set(
    ensureArray(payload?.claims)
      .map((claim) => String(claim?.id || '').trim())
      .filter(Boolean),
  );
}

function evaluatePolicyDecisionConsistency(payload, policyDecision) {
  if (!policyDecision) {
    return { checked: false, errors: [], warnings: [] };
  }
  const errors = [];
  const warnings = [];
  const claimIds = buildClaimIdSet(payload);
  const claimsById = new Map(
    ensureArray(payload?.claims)
      .map((claim) => [String(claim?.id || '').trim(), claim])
      .filter(([claimId]) => claimId),
  );
  const waiverClaimIds = new Set(
    ensureArray(payload?.waivers).flatMap((waiver) =>
      ensureArray(waiver?.relatedClaimIds).map((claimId) => String(claimId || '').trim()).filter(Boolean),
    ),
  );
  const assurance = policyDecision?.evaluation?.assurance;
  if (!assurance || typeof assurance !== 'object') {
    return { checked: true, errors, warnings: ['policy decision does not include evaluation.assurance'] };
  }

  for (const policyClaim of ensureArray(assurance.claims)) {
    const claimId = String(policyClaim?.claimId || '').trim();
    if (!claimId) continue;
    const claim = claimsById.get(claimId);
    if (!claim) {
      errors.push(`policy decision references missing claim: ${claimId}`);
      continue;
    }
    const result = String(policyClaim?.result || '').trim();
    const status = String(claim?.status || '').trim();
    if (result === 'waived' && status !== 'waived') {
      errors.push(`policy decision marks ${claimId} waived but change-package status is ${status}`);
    }
    if (result === 'pass' && ['waived', 'unresolved', 'failed'].includes(status)) {
      errors.push(`policy decision marks ${claimId} pass but change-package status is ${status}`);
    }
    if (result === 'block' && !['failed', 'unresolved'].includes(status)) {
      errors.push(`policy decision marks ${claimId} block but change-package status is ${status}`);
    }
    if (result === 'report-only' && status === 'waived') {
      errors.push(`policy decision marks ${claimId} report-only but change-package status is waived`);
    }
  }

  for (const waiver of ensureArray(assurance.waivers)) {
    const claimId = String(waiver?.claimId || '').trim();
    if (!claimId) continue;
    if (!claimIds.has(claimId)) {
      errors.push(`policy decision waiver references missing claim: ${claimId}`);
    } else if (!waiverClaimIds.has(claimId)) {
      errors.push(`policy decision waiver for ${claimId} is not represented in change-package waivers`);
    }
  }

  return { checked: true, errors, warnings };
}

function evaluateV2Consistency(payload, options) {
  if (!isChangePackageV2(payload)) {
    return {
      checked: false,
      claimCount: 0,
      proofObligationCount: 0,
      waiverCount: 0,
      missingArtifactRefs: [],
      errors: [],
      warnings: [],
      policyDecision: { checked: false, errors: [], warnings: [] },
    };
  }

  const errors = [];
  const warnings = [];
  const claims = ensureArray(payload?.claims);
  const claimIds = buildClaimIdSet(payload);
  if (claimIds.size !== claims.length) {
    errors.push('claims[].id must be unique and non-empty');
  }

  for (const [index, obligation] of ensureArray(payload?.proofObligations).entries()) {
    const claimId = String(obligation?.claimId || '').trim();
    if (!claimIds.has(claimId)) {
      errors.push(`proofObligations[${index}].claimId references missing claim: ${claimId || '(empty)'}`);
    }
  }

  for (const [index, waiver] of ensureArray(payload?.waivers).entries()) {
    for (const claimId of ensureArray(waiver?.relatedClaimIds)) {
      const normalizedClaimId = String(claimId || '').trim();
      if (!claimIds.has(normalizedClaimId)) {
        errors.push(`waivers[${index}].relatedClaimIds references missing claim: ${normalizedClaimId || '(empty)'}`);
      }
    }
  }

  for (const [index, counterexample] of ensureArray(payload?.counterexamples).entries()) {
    for (const claimId of ensureArray(counterexample?.claimIds)) {
      const normalizedClaimId = String(claimId || '').trim();
      if (!claimIds.has(normalizedClaimId)) {
        errors.push(`counterexamples[${index}].claimIds references missing claim: ${normalizedClaimId || '(empty)'}`);
      }
    }
  }

  const artifactRoot = resolveArtifactRoot(options, payload);
  const seenMissingArtifactRefs = new Set();
  const missingArtifactRefs = collectArtifactRefs(payload)
    .filter((entry) => !artifactExists(artifactRoot, entry.artifactRef))
    .filter((entry) => {
      const key = String(entry.artifactRef || '').trim();
      if (seenMissingArtifactRefs.has(key)) return false;
      seenMissingArtifactRefs.add(key);
      return true;
    });
  if (missingArtifactRefs.length > 0) {
    const message = `missing artifactRefs: ${missingArtifactRefs.map((entry) => entry.artifactRef).join(', ')}`;
    if (options.strict) {
      errors.push(message);
    } else {
      warnings.push(message);
    }
  }

  const policyDecision = evaluatePolicyDecisionConsistency(
    payload,
    readJsonOptional(options.policyDecisionPath),
  );
  errors.push(...policyDecision.errors);
  warnings.push(...policyDecision.warnings);

  return {
    checked: true,
    claimCount: claims.length,
    proofObligationCount: ensureArray(payload?.proofObligations).length,
    waiverCount: ensureArray(payload?.waivers).length,
    missingArtifactRefs,
    errors,
    warnings,
    policyDecision,
  };
}

function normalizeAjvErrors(errors) {
  return (errors || []).map((error) => {
    const instancePath = error.instancePath || '/';
    const keyword = error.keyword || 'unknown';
    const message = error.message || 'schema validation error';
    return `${instancePath} [${keyword}] ${message}`;
  });
}

function buildValidationReport(options, schemaResult, evidenceResult, v2Result) {
  const errors = [];
  const warnings = [];

  if (!schemaResult.ok) {
    errors.push(...normalizeAjvErrors(schemaResult.errors));
  }

  if (evidenceResult.missingRequiredEvidence.length > 0) {
    const message = `missing required evidence: ${evidenceResult.missingRequiredEvidence.map((item) => item.id).join(', ')}`;
    if (options.strict) {
      errors.push(message);
    } else {
      warnings.push(message);
    }
  }

  if (evidenceResult.countMismatches.length > 0) {
    warnings.push(...evidenceResult.countMismatches);
  }
  if (v2Result?.errors?.length > 0) {
    errors.push(...v2Result.errors);
  }
  if (v2Result?.warnings?.length > 0) {
    warnings.push(...v2Result.warnings);
  }

  const result = errors.length > 0 ? 'fail' : (warnings.length > 0 ? 'warn' : 'pass');
  return {
    schemaVersion: 'change-package-validation/v1',
    generatedAt: new Date().toISOString(),
    strict: options.strict,
    result,
    schema: {
      path: options.schemaPath,
      ok: schemaResult.ok,
      errors: normalizeAjvErrors(schemaResult.errors),
    },
    evidence: {
      requiredEvidenceIds: evidenceResult.requiredEvidenceIds,
      missingRequiredEvidence: evidenceResult.missingRequiredEvidence,
      itemCount: evidenceResult.itemCount,
      presentCountActual: evidenceResult.presentCountActual,
      missingCountActual: evidenceResult.missingCountActual,
    },
    v2: v2Result,
    errors,
    warnings,
  };
}

function renderMarkdown(report) {
  const lines = [
    '### Change Package Validation',
    `- result: ${report.result.toUpperCase()}`,
    `- strict: ${report.strict}`,
    `- schema: ${report.schema.ok ? 'PASS' : 'FAIL'}`,
    `- required evidence: ${report.evidence.requiredEvidenceIds.length > 0 ? report.evidence.requiredEvidenceIds.join(', ') : '(none)'}`,
    `- missing required evidence: ${report.evidence.missingRequiredEvidence.length > 0 ? report.evidence.missingRequiredEvidence.map((item) => item.id).join(', ') : '(none)'}`,
    `- evidence present/missing(actual): ${report.evidence.presentCountActual}/${report.evidence.missingCountActual}`,
  ];
  if (report.v2?.checked) {
    lines.push(`- v2 consistency: claims=${report.v2.claimCount}, proofObligations=${report.v2.proofObligationCount}, waivers=${report.v2.waiverCount}`);
    lines.push(`- v2 missing artifactRefs: ${report.v2.missingArtifactRefs.length > 0 ? report.v2.missingArtifactRefs.map((entry) => entry.artifactRef).join(', ') : '(none)'}`);
    lines.push(`- v2 policy decision consistency: ${report.v2.policyDecision?.checked ? 'checked' : 'not checked'}`);
  }

  if (report.errors.length > 0) {
    lines.push('- errors:');
    for (const error of report.errors) {
      lines.push(`  - ${error}`);
    }
  }
  if (report.warnings.length > 0) {
    lines.push('- warnings:');
    for (const warning of report.warnings) {
      lines.push(`  - ${warning}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

function persistReport(report, markdown, options) {
  ensureDirectory(options.outputJsonPath);
  fs.writeFileSync(options.outputJsonPath, `${JSON.stringify(report, null, 2)}\n`);

  ensureDirectory(options.outputMarkdownPath);
  fs.writeFileSync(options.outputMarkdownPath, `${markdown.trimEnd()}\n`);
}

async function run(options = parseArgs(process.argv)) {
  if (options.help) {
    printHelp();
    return null;
  }

  const payload = readJsonFile(options.inputPath);
  options.schemaPath = resolveSchemaPath(options, payload);
  const schema = readJsonFile(options.schemaPath);
  const schemaResult = validateSchema(schema, payload);
  const requiredEvidenceIds = resolveRequiredEvidenceIds(options, payload);
  const evidenceResult = evaluateEvidence(payload, requiredEvidenceIds);
  const v2Result = evaluateV2Consistency(payload, options);
  const report = buildValidationReport(options, schemaResult, evidenceResult, v2Result);
  const markdown = renderMarkdown(report);
  persistReport(report, markdown, options);

  process.stdout.write(markdown);
  if (report.result === 'fail') {
    process.exitCode = 1;
  }
  return report;
}

function isDirectExecution() {
  const entry = process.argv[1];
  if (!entry) return false;
  return import.meta.url === pathToFileURL(resolve(entry)).href;
}

if (isDirectExecution()) {
  try {
    await run();
  } catch (error) {
    const message = error instanceof Error ? error.stack || error.message : String(error);
    process.stderr.write(`[change-package:validate] ${message}\n`);
    process.exit(1);
  }
}

export {
  buildValidationReport,
  parseArgs,
  renderMarkdown,
  run,
};
