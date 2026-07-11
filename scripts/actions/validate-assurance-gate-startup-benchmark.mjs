#!/usr/bin/env node

import { readFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import {
  assessOptimization,
  summarizeSamples,
} from './benchmark-assurance-gate-startup.mjs';

const DEFAULT_REPORT = 'artifacts/benchmarks/assurance-gate-startup.json';
const DEFAULT_SCHEMA = 'schema/assurance-gate-startup-benchmark.schema.json';

function formatErrors(errors = []) {
  return errors
    .map((entry) => `${entry.instancePath || '/'}: ${entry.message || 'invalid'}`)
    .join('\n');
}

const PHASES = [
  'actionInitialization',
  'corepackPnpmSetup',
  'dependencyInstall',
  'coreBuild',
  'gateExecution',
  'reviewSurfaceRendering',
  'total',
];

function semanticError(instancePath, message) {
  return { instancePath, message };
}

function sameNumber(left, right) {
  return Number.isFinite(left)
    && Number.isFinite(right)
    && Math.abs(left - right) <= Math.max(1e-9, Math.abs(right) * 1e-12);
}

function validateSummary(actual, expected, cacheState) {
  const errors = [];
  const base = `/summary/${cacheState}`;
  if (actual.sampleCount !== expected.sampleCount) {
    errors.push(semanticError(`${base}/sampleCount`, 'must equal the measured sample count'));
  }
  for (const result of ['pass', 'block', 'error']) {
    if (actual.results[result] !== expected.results[result]) {
      errors.push(semanticError(`${base}/results/${result}`, 'must equal the measured result count'));
    }
  }
  if (expected.phaseTimingsMs === null) {
    if (actual.phaseTimingsMs !== null) {
      errors.push(semanticError(`${base}/phaseTimingsMs`, 'must be null when no samples were collected'));
    }
    return errors;
  }
  if (actual.phaseTimingsMs === null) {
    errors.push(semanticError(`${base}/phaseTimingsMs`, 'must summarize collected samples'));
    return errors;
  }
  for (const phase of PHASES) {
    for (const statistic of ['minimum', 'median', 'maximum', 'p90']) {
      if (!sameNumber(
        actual.phaseTimingsMs[phase][statistic],
        expected.phaseTimingsMs[phase][statistic],
      )) {
        errors.push(semanticError(
          `${base}/phaseTimingsMs/${phase}/${statistic}`,
          'must be derived from the measured samples',
        ));
      }
    }
  }
  return errors;
}

export function validateBenchmarkSemantics(report) {
  const errors = [];
  const expectedPerState = report.method.runCountPerCacheState;
  for (const cacheState of ['cold', 'warm']) {
    const samples = report.samples.filter((sample) => sample.cacheState === cacheState);
    const collectionError = report.collectionErrors.find((entry) => entry.cacheState === cacheState);
    if (samples.length > expectedPerState) {
      errors.push(semanticError(
        '/samples',
        `must not contain more than ${expectedPerState} ${cacheState} samples`,
      ));
    }
    const missingSampleCount = expectedPerState - samples.length;
    if (missingSampleCount > 0 && collectionError?.missingSampleCount !== missingSampleCount) {
      errors.push(semanticError(
        '/collectionErrors',
        `must account for ${missingSampleCount} missing ${cacheState} samples`,
      ));
    }
    if (missingSampleCount === 0 && collectionError) {
      errors.push(semanticError(
        '/collectionErrors',
        `must not report a ${cacheState} collection error when all samples exist`,
      ));
    }
    const indices = samples.map((sample) => sample.index).sort((left, right) => left - right);
    const expectedIndices = Array.from({ length: samples.length }, (_, index) => index + 1);
    if (JSON.stringify(indices) !== JSON.stringify(expectedIndices)) {
      errors.push(semanticError(
        '/samples',
        `${cacheState} sample indices must be unique and contiguous from 1`,
      ));
    }
    for (const sample of samples) {
      if (sample.result !== 'error' && sample.result !== report.fixture.expectedResult) {
        errors.push(semanticError(
          `/samples/${report.samples.indexOf(sample)}/result`,
          'must preserve the fixture expected result',
        ));
      }
      const measuredSubtotal = sample.phaseTimingsMs.actionInitialization
        + sample.phaseTimingsMs.corepackPnpmSetup
        + sample.phaseTimingsMs.dependencyInstall
        + sample.phaseTimingsMs.coreBuild
        + sample.phaseTimingsMs.gateExecution;
      if (sample.phaseTimingsMs.total < measuredSubtotal) {
        errors.push(semanticError(
          `/samples/${report.samples.indexOf(sample)}/phaseTimingsMs/total`,
          'must include all non-overlapping measured phases',
        ));
      }
    }
    errors.push(...validateSummary(
      report.summary[cacheState],
      summarizeSamples(samples),
      cacheState,
    ));
  }

  if (report.summary.cold.phaseTimingsMs === null) {
    errors.push(semanticError(
      '/summary/cold/phaseTimingsMs',
      'cold samples are required to evaluate the optimization decision',
    ));
    return errors;
  }
  const expectedAssessment = assessOptimization(report.summary, report.method.pilotFriction);
  for (const trigger of Object.keys(expectedAssessment.triggers)) {
    if (report.optimizationAssessment.triggers[trigger] !== expectedAssessment.triggers[trigger]) {
      errors.push(semanticError(
        `/optimizationAssessment/triggers/${trigger}`,
        'must be derived from the benchmark summary and pilot-friction input',
      ));
    }
  }
  if (!sameNumber(
    report.optimizationAssessment.setupInstallBuildShare,
    expectedAssessment.setupInstallBuildShare,
  )) {
    errors.push(semanticError(
      '/optimizationAssessment/setupInstallBuildShare',
      'must be derived from the cold median phase timings',
    ));
  }
  if (report.optimizationAssessment.recommendedOutcome !== expectedAssessment.recommendedOutcome) {
    errors.push(semanticError(
      '/optimizationAssessment/recommendedOutcome',
      'must follow the optimization trigger decision rule',
    ));
  }
  return errors;
}

export function validateBenchmarkFiles({
  reportPath = DEFAULT_REPORT,
  schemaPath = DEFAULT_SCHEMA,
  cwd = process.cwd(),
} = {}) {
  const report = JSON.parse(readFileSync(path.resolve(cwd, reportPath), 'utf8'));
  const schema = JSON.parse(readFileSync(path.resolve(cwd, schemaPath), 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const schemaValid = validate(report);
  const schemaErrors = validate.errors ?? [];
  const semanticErrors = schemaValid ? validateBenchmarkSemantics(report) : [];
  return {
    valid: schemaValid && semanticErrors.length === 0,
    report,
    errors: [...schemaErrors, ...semanticErrors],
  };
}

export function run(argv = process.argv) {
  const reportPath = argv[2] ?? DEFAULT_REPORT;
  const schemaPath = argv[3] ?? DEFAULT_SCHEMA;
  const result = validateBenchmarkFiles({ reportPath, schemaPath });
  if (!result.valid) {
    process.stderr.write(`Assurance Gate startup benchmark validation: FAILED\n${formatErrors(result.errors)}\n`);
    return 1;
  }
  process.stdout.write('Assurance Gate startup benchmark validation: OK\n');
  process.stdout.write(`- report: ${reportPath}\n`);
  process.stdout.write(`- schema: ${schemaPath}\n`);
  process.stdout.write(`- samples: ${result.report.samples.length}\n`);
  return 0;
}

function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath) return false;
  return path.resolve(fileURLToPath(metaUrl)) === path.resolve(argvPath);
}

if (isExecutedAsMain(import.meta.url)) {
  try {
    process.exitCode = run();
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`Assurance Gate startup benchmark validation: FAILED\n${message}\n`);
    process.exitCode = 1;
  }
}
