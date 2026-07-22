#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { getFormalRunnerProducer, hasEligibleToolVersion } from '../formal/execution-evidence.mjs';

const REPORT_PRODUCER = getFormalRunnerProducer('model');
const TOP_LEVEL_KEYS = new Set([
  'schemaVersion', 'artifactStatus', 'status', 'ok', 'generatedAtUtc', 'producer',
  'detectedInputs', 'executedInputs', 'skippedInputs', 'approvedSkipRefs', 'tlc', 'alloy',
]);
const BACKEND_KEYS = new Set(['results', 'skipped', 'errors']);
const RESULT_KEYS = {
  tlc: new Set(['module', 'ok', 'code', 'log', 'config', 'executionStatus', 'error', 'evidence']),
  alloy: new Set(['file', 'ok', 'code', 'signal', 'timeout', 'log', 'executionStatus', 'error', 'evidence']),
};
const EVIDENCE_KEYS = new Set([
  'schemaVersion', 'artifactStatus', 'producer', 'provenance', 'executionOccurred',
  'tool', 'input', 'result', 'scope', 'assumptions',
]);
const TOOL_KEYS = new Set([
  'name', 'version', 'versionStatus', 'versionSource', 'artifactSha256', 'expectedArtifactSha256',
]);
const EVIDENCE_RESULT_KEYS = new Set(['status', 'code', 'logPath']);

const isObject = (value) => value !== null && typeof value === 'object' && !Array.isArray(value);
const isNonEmptyString = (value) => typeof value === 'string' && value.trim().length > 0;
const isNonNegativeInteger = (value) => Number.isInteger(value) && value >= 0;
const exactBinding = (actual, expected) => isObject(actual)
  && actual.id === expected.id
  && actual.version === expected.version
  && actual.contract === expected.contract
  && actual.artifactRef === expected.artifactRef
  && Object.keys(actual).length === 4;
const unexpectedKeys = (value, allowed) => isObject(value)
  ? Object.keys(value).filter((key) => !allowed.has(key))
  : [];
const isSafeArtifactPath = (value) => isNonEmptyString(value)
  && !path.isAbsolute(value)
  && !value.split(/[\\/]/u).includes('..');

function validateExecutionEvidence(evidence, result, location, errors) {
  if (!isObject(evidence)) {
    errors.push(`${location}.evidence must be an object`);
    return;
  }
  const extraEvidenceKeys = unexpectedKeys(evidence, EVIDENCE_KEYS);
  if (extraEvidenceKeys.length > 0) errors.push(`${location}.evidence has unexpected keys: ${extraEvidenceKeys.join(', ')}`);
  if (evidence.schemaVersion !== 'formal-runner-result/v1') errors.push(`${location}.evidence.schemaVersion is invalid`);
  if (evidence.artifactStatus !== 'execution-report') errors.push(`${location}.evidence.artifactStatus must be execution-report`);
  if (!exactBinding(evidence.producer, REPORT_PRODUCER)) errors.push(`${location}.evidence.producer is not the reviewed model runner`);
  if (evidence.provenance !== 'runner-reported') errors.push(`${location}.evidence.provenance is invalid`);
  if (evidence.executionOccurred !== true) errors.push(`${location}.evidence.executionOccurred must be true`);

  if (!isObject(evidence.tool)) {
    errors.push(`${location}.evidence.tool must be an object`);
  } else {
    const extraToolKeys = unexpectedKeys(evidence.tool, TOOL_KEYS);
    if (extraToolKeys.length > 0) errors.push(`${location}.evidence.tool has unexpected keys: ${extraToolKeys.join(', ')}`);
    if (!isNonEmptyString(evidence.tool.name)) errors.push(`${location}.evidence.tool.name is required`);
    if (!isNonEmptyString(evidence.tool.version)) errors.push(`${location}.evidence.tool.version is required`);
    if (!['verified', 'unknown', 'mismatch'].includes(evidence.tool.versionStatus)) errors.push(`${location}.evidence.tool.versionStatus is invalid`);
    if (!['cli', 'jar-manifest', 'package-manifest', 'reviewed-pin', 'unavailable'].includes(evidence.tool.versionSource)) {
      errors.push(`${location}.evidence.tool.versionSource is invalid`);
    }
    if (evidence.tool.versionStatus === 'verified' && !hasEligibleToolVersion(evidence.tool)) {
      errors.push(`${location}.evidence.tool has contradictory or incomplete verified provenance`);
    }
    for (const key of ['artifactSha256', 'expectedArtifactSha256']) {
      if (evidence.tool[key] !== undefined && !/^[a-f0-9]{64}$/u.test(evidence.tool[key])) {
        errors.push(`${location}.evidence.tool.${key} is invalid`);
      }
    }
  }

  if (!Array.isArray(evidence.input) || evidence.input.length === 0 || !evidence.input.every(isSafeArtifactPath)) {
    errors.push(`${location}.evidence.input must contain safe repository-relative paths`);
  } else if (location.startsWith('alloy.') && !evidence.input.includes(result.file)) {
    errors.push(`${location}.evidence.input does not bind the recorded Alloy file`);
  } else if (location.startsWith('tlc.')
    && (!evidence.input.includes(result.config)
      || !evidence.input.some((inputPath) => path.basename(inputPath, path.extname(inputPath)) === result.module))) {
    errors.push(`${location}.evidence.input does not bind the recorded TLC module and configuration`);
  }
  if (!isObject(evidence.result)) {
    errors.push(`${location}.evidence.result must be an object`);
  } else {
    const extraResultKeys = unexpectedKeys(evidence.result, EVIDENCE_RESULT_KEYS);
    if (extraResultKeys.length > 0) errors.push(`${location}.evidence.result has unexpected keys: ${extraResultKeys.join(', ')}`);
    const expectedStatus = result.executionStatus === 'timeout'
      ? 'timeout'
      : result.executionStatus === 'tool-error'
        ? 'tool-error'
        : result.ok ? 'ok' : 'failed';
    if (evidence.result.status !== expectedStatus) errors.push(`${location}.evidence.result.status does not match the runner result`);
    if (!(Number.isInteger(evidence.result.code) || evidence.result.code === null)) errors.push(`${location}.evidence.result.code is invalid`);
    if (!isSafeArtifactPath(evidence.result.logPath)) errors.push(`${location}.evidence.result.logPath must be a safe repository-relative path`);
    if (evidence.result.code !== result.code) errors.push(`${location}.evidence.result.code does not match the runner result`);
    if (evidence.result.logPath !== result.log) errors.push(`${location}.evidence.result.logPath does not match the runner result`);
    if (evidence.result.status === 'ok' && evidence.result.code !== 0) errors.push(`${location}.evidence successful result must have code 0`);
  }
  if (!isNonEmptyString(evidence.scope)) errors.push(`${location}.evidence.scope is required`);
  if (!Array.isArray(evidence.assumptions) || evidence.assumptions.length === 0 || !evidence.assumptions.every(isNonEmptyString)) {
    errors.push(`${location}.evidence.assumptions must be non-empty`);
  }
}

export function validateModelCheckReportContract(report) {
  const errors = [];
  if (!isObject(report)) return ['report must be an object'];
  const extraTopLevelKeys = unexpectedKeys(report, TOP_LEVEL_KEYS);
  if (extraTopLevelKeys.length > 0) errors.push(`report has unexpected keys: ${extraTopLevelKeys.join(', ')}`);
  if (report.schemaVersion !== 'model-check-report/v1') errors.push('schemaVersion must be model-check-report/v1');
  if (report.artifactStatus !== 'execution-report') errors.push('artifactStatus must be execution-report');
  if (!['executed', 'failed', 'tool-error', 'not-run'].includes(report.status)) errors.push('status is invalid');
  if (!(typeof report.ok === 'boolean' || report.ok === null)) errors.push('ok must be boolean or null');
  if (!isNonEmptyString(report.generatedAtUtc) || Number.isNaN(Date.parse(report.generatedAtUtc))) errors.push('generatedAtUtc is invalid');
  if (!exactBinding(report.producer, REPORT_PRODUCER)) errors.push('producer is not the reviewed model runner');
  for (const counter of ['detectedInputs', 'executedInputs', 'skippedInputs']) {
    if (!isNonNegativeInteger(report[counter])) errors.push(`${counter} must be a non-negative integer`);
  }
  if (!Array.isArray(report.approvedSkipRefs) || !report.approvedSkipRefs.every(isNonEmptyString)
    || new Set(report.approvedSkipRefs).size !== report.approvedSkipRefs.length) {
    errors.push('approvedSkipRefs must be a unique string array');
  }

  const allResults = [];
  let observedSkipped = 0;
  let backendErrorCount = 0;
  for (const backendName of ['tlc', 'alloy']) {
    const backend = report[backendName];
    if (!isObject(backend)) {
      errors.push(`${backendName} must be an object`);
      continue;
    }
    const extraBackendKeys = unexpectedKeys(backend, BACKEND_KEYS);
    if (extraBackendKeys.length > 0) errors.push(`${backendName} has unexpected keys: ${extraBackendKeys.join(', ')}`);
    if (!Array.isArray(backend.results)) errors.push(`${backendName}.results must be an array`);
    if (!Array.isArray(backend.skipped) || !backend.skipped.every(isNonEmptyString)) errors.push(`${backendName}.skipped must be a string array`);
    if (!Array.isArray(backend.errors)) errors.push(`${backendName}.errors must be an array`);
    observedSkipped += Array.isArray(backend.skipped) ? backend.skipped.length : 0;
    backendErrorCount += Array.isArray(backend.errors) ? backend.errors.length : 0;
    for (const [index, entry] of (Array.isArray(backend.errors) ? backend.errors : []).entries()) {
      if (!isObject(entry) || !isNonEmptyString(entry.file) || !isNonEmptyString(entry.error)
        || unexpectedKeys(entry, new Set(['file', 'error'])).length > 0) {
        errors.push(`${backendName}.errors[${index}] is invalid`);
      }
    }
    for (const [index, result] of (Array.isArray(backend.results) ? backend.results : []).entries()) {
      const location = `${backendName}.results[${index}]`;
      allResults.push(result);
      if (!isObject(result)) {
        errors.push(`${location} must be an object`);
        continue;
      }
      const extraResultKeys = unexpectedKeys(result, RESULT_KEYS[backendName]);
      if (extraResultKeys.length > 0) errors.push(`${location} has unexpected keys: ${extraResultKeys.join(', ')}`);
      const identityKey = backendName === 'tlc' ? 'module' : 'file';
      if (!isNonEmptyString(result[identityKey])) errors.push(`${location}.${identityKey} is required`);
      if (typeof result.ok !== 'boolean') errors.push(`${location}.ok must be boolean`);
      if (!(Number.isInteger(result.code) || result.code === null)) errors.push(`${location}.code is invalid`);
      if (!isSafeArtifactPath(result.log)) errors.push(`${location}.log must be a safe repository-relative path`);
      if (!['executed', 'tool-error', 'timeout'].includes(result.executionStatus)) errors.push(`${location}.executionStatus is invalid`);
      if (backendName === 'tlc' && !isSafeArtifactPath(result.config)) errors.push(`${location}.config must be a safe repository-relative path`);
      if (backendName === 'alloy' && (typeof result.timeout !== 'boolean' || !(isNonEmptyString(result.signal) || result.signal === null))) {
        errors.push(`${location}.timeout or signal is invalid`);
      }
      if (backendName === 'alloy' && result.timeout !== (result.executionStatus === 'timeout')) {
        errors.push(`${location}.timeout does not match executionStatus`);
      }
      if (result.error !== undefined && !isNonEmptyString(result.error)) errors.push(`${location}.error must be non-empty when present`);
      if (result.executionStatus === 'tool-error' && !isNonEmptyString(result.error)) {
        errors.push(`${location}.tool-error requires a bounded error description`);
      }
      validateExecutionEvidence(result.evidence, result, location, errors);
    }
  }

  const observedExecuted = allResults.filter((result) => result?.executionStatus === 'executed').length;
  if (isNonNegativeInteger(report.executedInputs) && report.executedInputs !== observedExecuted) {
    errors.push(`executedInputs=${report.executedInputs} does not match observed executed results=${observedExecuted}`);
  }
  if (isNonNegativeInteger(report.skippedInputs) && report.skippedInputs !== observedSkipped) {
    errors.push(`skippedInputs=${report.skippedInputs} does not match observed skipped inputs=${observedSkipped}`);
  }
  if (isNonNegativeInteger(report.detectedInputs)
    && report.detectedInputs < allResults.length + observedSkipped) {
    errors.push('detectedInputs is smaller than recorded results plus skipped inputs');
  }
  if (report.status === 'executed' && (report.ok !== true || observedExecuted === 0 || backendErrorCount > 0
    || allResults.some((result) => result?.executionStatus !== 'executed' || result?.ok !== true))) {
    errors.push('executed status is inconsistent with the recorded results');
  }
  if (report.status === 'failed' && report.ok !== false) errors.push('failed status requires ok=false');
  if (['tool-error', 'not-run'].includes(report.status) && report.ok !== null) errors.push(`${report.status} status requires ok=null`);
  if (report.status === 'not-run' && (allResults.length > 0 || backendErrorCount > 0 || observedExecuted > 0)) {
    errors.push('not-run status cannot contain results, backend errors, or executions');
  }
  if (report.status === 'tool-error' && backendErrorCount === 0
    && !allResults.some((result) => result?.executionStatus === 'tool-error')) {
    errors.push('tool-error status requires a backend error or tool-error result');
  }
  return errors;
}

export function evaluateModelCheckEnforcement(report) {
  const errors = validateModelCheckReportContract(report);
  if (errors.length > 0) return errors;
  const results = [...report.tlc.results, ...report.alloy.results];
  const backendErrors = report.tlc.errors.length + report.alloy.errors.length;
  if (report.status !== 'executed' || report.ok !== true) errors.push('report must record an all-pass executed run');
  if (report.detectedInputs < 1) errors.push('at least one formal input must be detected');
  if (report.executedInputs < 1) errors.push('at least one actual checker execution is required');
  if (backendErrors > 0) errors.push('tool preparation and runner errors must be zero');
  if (report.skippedInputs > 0) errors.push(`unapproved skipped inputs must be zero (observed ${report.skippedInputs})`);
  if (report.approvedSkipRefs.length > 0) errors.push('approved skip exceptions are not supported by this contract');
  if (report.detectedInputs !== report.executedInputs) errors.push('every detected formal input must be executed');
  for (const [index, result] of results.entries()) {
    const evidence = result.evidence;
    if (result.executionStatus !== 'executed' || result.ok !== true || evidence?.result?.status !== 'ok') {
      errors.push(`result[${index}] is not an all-pass actual execution`);
    }
    if (!hasEligibleToolVersion(evidence?.tool)) {
      errors.push(`result[${index}] has an ineligible tool-version provenance`);
    }
  }
  return errors;
}

function main(argv = process.argv.slice(2)) {
  const contractOnly = argv.includes('--contract-only');
  const file = argv.find((value) => value !== '--contract-only');
  if (!file) {
    console.error('Usage: node scripts/verify/enforce-model-check-report.mjs [--contract-only] <model-check.json>');
    return 2;
  }
  let report;
  try {
    report = JSON.parse(fs.readFileSync(file, 'utf8'));
  } catch (error) {
    console.error(`Unable to read model-check report: ${error instanceof Error ? error.message : String(error)}`);
    return 1;
  }
  const errors = contractOnly
    ? validateModelCheckReportContract(report)
    : evaluateModelCheckEnforcement(report);
  if (errors.length > 0) {
    console.error(`${contractOnly ? 'Model-check report contract' : 'Formal enforcement'} failed:`);
    for (const error of errors) console.error(`- ${error}`);
    return 1;
  }
  console.log(contractOnly ? 'Model-check report contract is valid' : 'Formal enforcement passed');
  return 0;
}

const invokedPath = process.argv[1] ? path.resolve(process.argv[1]) : '';
if (invokedPath === fileURLToPath(import.meta.url)) {
  process.exit(main());
}
