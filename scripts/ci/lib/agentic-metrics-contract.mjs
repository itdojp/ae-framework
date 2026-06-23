const RATIO_TOLERANCE = 0.0001;
const NOT_COLLECTED = 'not_collected';

function createError(keyword, instancePath, message) {
  return { keyword, instancePath, message };
}

function isObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function ratioMatches(actual, expected) {
  return typeof actual === 'number' && Math.abs(actual - expected) <= RATIO_TOLERANCE;
}

function validateCountRatioMetric({
  metric,
  basePath,
  numeratorField,
  denominatorField,
  ratioField,
  zeroDenominatorRatio,
  errors,
}) {
  if (!isObject(metric)) {
    return;
  }

  const numerator = metric[numeratorField];
  const denominator = metric[denominatorField];
  const ratio = metric[ratioField];

  if (!Number.isInteger(numerator) || !Number.isInteger(denominator)) {
    return;
  }

  if (numerator > denominator) {
    errors.push(createError(
      'metric_count_order',
      `${basePath}/${numeratorField}`,
      `${numeratorField} must be less than or equal to ${denominatorField} (${denominator}), got ${numerator}`,
    ));
  }

  const expectedRatio = denominator === 0 ? zeroDenominatorRatio : numerator / denominator;
  if (!ratioMatches(ratio, expectedRatio)) {
    errors.push(createError(
      'metric_ratio_mismatch',
      `${basePath}/${ratioField}`,
      `${ratioField} must equal ${numeratorField}/${denominatorField} within tolerance ${RATIO_TOLERANCE}; expected ${expectedRatio}, got ${ratio}`,
    ));
  }
}

function validateClaimCoverage(metrics, errors) {
  validateCountRatioMetric({
    metric: metrics?.claim_coverage,
    basePath: '/agentPrAssurance/metrics/claim_coverage',
    numeratorField: 'numerator',
    denominatorField: 'denominator',
    ratioField: 'ratio',
    zeroDenominatorRatio: 1,
    errors,
  });
}

function validateRequiredLaneCompliance(metrics, errors) {
  const metric = metrics?.required_lane_compliance;
  if (!isObject(metric)) {
    return;
  }

  const basePath = '/agentPrAssurance/metrics/required_lane_compliance';
  const satisfied = metric.satisfied;
  const required = metric.required;
  const ratio = metric.ratio;

  if (!Number.isInteger(satisfied) || !Number.isInteger(required)) {
    return;
  }

  if (satisfied > required) {
    errors.push(createError(
      'metric_count_order',
      `${basePath}/satisfied`,
      `satisfied must be less than or equal to required (${required}), got ${satisfied}`,
    ));
  }

  if (required === 0) {
    if (satisfied !== 0) {
      errors.push(createError(
        'metric_zero_denominator',
        `${basePath}/satisfied`,
        `satisfied must be 0 when required is 0, got ${satisfied}`,
      ));
    }
    if (ratio !== null) {
      errors.push(createError(
        'metric_not_applicable_ratio',
        `${basePath}/ratio`,
        `ratio must be null when required is 0, got ${ratio}`,
      ));
    }
    if (metric.notApplicable !== true) {
      errors.push(createError(
        'metric_not_applicable_flag',
        `${basePath}/notApplicable`,
        'notApplicable must be true when required is 0',
      ));
    }
  } else {
    const expectedRatio = satisfied / required;
    if (!ratioMatches(ratio, expectedRatio)) {
      errors.push(createError(
        'metric_ratio_mismatch',
        `${basePath}/ratio`,
        `ratio must equal satisfied/required within tolerance ${RATIO_TOLERANCE}; expected ${expectedRatio}, got ${ratio}`,
      ));
    }
    if (metric.notApplicable === true) {
      errors.push(createError(
        'metric_not_applicable_flag',
        `${basePath}/notApplicable`,
        'notApplicable must be absent or false when required is greater than 0',
      ));
    }
  }

  if (satisfied === required && Array.isArray(metric.missingLanes) && metric.missingLanes.length > 0) {
    errors.push(createError(
      'metric_missing_lanes_contradiction',
      `${basePath}/missingLanes`,
      'missingLanes must be empty or absent when all required lanes are satisfied',
    ));
  }
}

function validateEvidenceCompleteness(metrics, errors) {
  validateCountRatioMetric({
    metric: metrics?.evidence_completeness,
    basePath: '/agentPrAssurance/metrics/evidence_completeness',
    numeratorField: 'present',
    denominatorField: 'required',
    ratioField: 'ratio',
    zeroDenominatorRatio: 1,
    errors,
  });
}

function validateFalseBlockRate(metrics, errors) {
  const metric = metrics?.false_block_rate;
  if (!isObject(metric)) {
    return;
  }

  const basePath = '/agentPrAssurance/metrics/false_block_rate';
  const annotatedFalseBlocks = metric.annotatedFalseBlocks;
  const totalBlocks = metric.totalBlocks;
  const ratio = metric.ratio;

  if (!Number.isInteger(totalBlocks)) {
    return;
  }

  if (Number.isInteger(annotatedFalseBlocks)) {
    if (annotatedFalseBlocks > totalBlocks) {
      errors.push(createError(
        'metric_count_order',
        `${basePath}/annotatedFalseBlocks`,
        `annotatedFalseBlocks must be less than or equal to totalBlocks (${totalBlocks}), got ${annotatedFalseBlocks}`,
      ));
    }
    if (totalBlocks === 0) {
      if (ratio !== null) {
        errors.push(createError(
          'metric_zero_denominator_ratio',
          `${basePath}/ratio`,
          `ratio must be null when totalBlocks is 0, got ${ratio}`,
        ));
      }
    } else {
      const expectedRatio = annotatedFalseBlocks / totalBlocks;
      if (!ratioMatches(ratio, expectedRatio)) {
        errors.push(createError(
          'metric_ratio_mismatch',
          `${basePath}/ratio`,
          `ratio must equal annotatedFalseBlocks/totalBlocks within tolerance ${RATIO_TOLERANCE}; expected ${expectedRatio}, got ${ratio}`,
        ));
      }
    }
  } else if (annotatedFalseBlocks === null) {
    if (ratio !== null) {
      errors.push(createError(
        'metric_unannotated_ratio',
        `${basePath}/ratio`,
        `ratio must be null when annotatedFalseBlocks is null, got ${ratio}`,
      ));
    }
    if (metric.annotationRequired !== true) {
      errors.push(createError(
        'metric_annotation_required',
        `${basePath}/annotationRequired`,
        'annotationRequired must be true when annotatedFalseBlocks is null',
      ));
    }
  }
}

function countClassification(entries, classification) {
  return entries.filter((entry) => entry?.classification === classification).length;
}

function sumField(entries, field) {
  return entries.reduce((total, entry) => total + (Number.isInteger(entry?.[field]) ? entry[field] : 0), 0);
}

const REQUIRED_CHECK_COLLECTIBLE_SUMMARY_FIELDS = [
  'success_count',
  'pending_count',
  'current_required_failure_count',
  'policy_semantic_failure_count',
  'operational_failure_count',
  'manual_rerun_required_count',
  'stale_or_superseded_failure_count',
  'stale_cancelled_count',
  'superseded_count',
  'same_head_stale_count',
  'semantic_blocking_failure_count',
  'operational_note_count',
];

const AGENT_REGRESSION_COLLECTIBLE_FIELDS = [
  'currentFailures',
  'staleOrSupersededFailures',
  'operationalNotes',
  'currentRequiredFailures',
  'policySemanticFailures',
  'manualRerunRequired',
];

function validateExactFieldValue(object, {
  field,
  expected,
  basePath,
  keyword,
  messagePrefix,
  errors,
}) {
  if (object?.[field] === expected) {
    return;
  }
  errors.push(createError(
    keyword,
    `${basePath}/${field}`,
    `${messagePrefix} ${field} must equal ${expected}, got ${object?.[field]}`,
  ));
}

function validateNotCollectedRequiredChecks(requiredChecks, productMetrics, metrics, errors) {
  const required = Array.isArray(requiredChecks.required) ? requiredChecks.required : [];
  const summary = requiredChecks.summary;
  if (!isObject(summary)) {
    return;
  }

  const basePath = '/agentPrAssurance/productMetrics/required_checks/summary';
  validateExactFieldValue(summary, {
    field: 'required_count',
    expected: required.length,
    basePath,
    keyword: 'required_check_summary_mismatch',
    messagePrefix: 'not_collected required checks',
    errors,
  });
  validateExactFieldValue(summary, {
    field: 'collected_count',
    expected: 0,
    basePath,
    keyword: 'required_check_summary_mismatch',
    messagePrefix: 'not_collected required checks',
    errors,
  });

  for (const field of REQUIRED_CHECK_COLLECTIBLE_SUMMARY_FIELDS) {
    validateExactFieldValue(summary, {
      field,
      expected: NOT_COLLECTED,
      basePath,
      keyword: 'required_check_summary_mismatch',
      messagePrefix: 'not_collected required checks',
      errors,
    });
  }

  if (productMetrics?.ci_rerun_count !== NOT_COLLECTED) {
    errors.push(createError(
      'ci_rerun_count_mismatch',
      '/agentPrAssurance/productMetrics/ci_rerun_count',
      `ci_rerun_count must be ${NOT_COLLECTED} when required checks are not collected, got ${productMetrics?.ci_rerun_count}`,
    ));
  }

  if (productMetrics?.ci_rerun_classification_counts !== NOT_COLLECTED) {
    errors.push(createError(
      'ci_rerun_classification_counts_mismatch',
      '/agentPrAssurance/productMetrics/ci_rerun_classification_counts',
      `ci_rerun_classification_counts must be ${NOT_COLLECTED} when required checks are not collected, got ${productMetrics?.ci_rerun_classification_counts}`,
    ));
  }

  const regressionSignal = metrics?.agent_regression_signal;
  if (isObject(regressionSignal)) {
    for (const field of AGENT_REGRESSION_COLLECTIBLE_FIELDS) {
      validateExactFieldValue(regressionSignal, {
        field,
        expected: NOT_COLLECTED,
        basePath: '/agentPrAssurance/metrics/agent_regression_signal',
        keyword: 'agent_regression_not_collected_mismatch',
        messagePrefix: 'not_collected regression signal',
        errors,
      });
    }
    validateExactFieldValue(regressionSignal, {
      field: 'classificationSource',
      expected: NOT_COLLECTED,
      basePath: '/agentPrAssurance/metrics/agent_regression_signal',
      keyword: 'agent_regression_not_collected_mismatch',
      messagePrefix: 'not_collected regression signal',
      errors,
    });
  }
}

function validateRequiredChecks(productMetrics, metrics, errors) {
  const requiredChecks = productMetrics?.required_checks;
  if (!isObject(requiredChecks)) {
    return;
  }

  const required = Array.isArray(requiredChecks.required) ? requiredChecks.required : [];
  const summary = requiredChecks.summary;
  if (!isObject(summary)) {
    return;
  }

  if (requiredChecks.source === NOT_COLLECTED) {
    validateNotCollectedRequiredChecks(requiredChecks, productMetrics, metrics, errors);
    return;
  }

  const basePath = '/agentPrAssurance/productMetrics/required_checks/summary';
  const expected = {
    required_count: required.length,
    collected_count: required.filter((entry) => entry?.collected === true).length,
    success_count: countClassification(required, 'success'),
    pending_count: countClassification(required, 'pending'),
    current_required_failure_count: countClassification(required, 'current_required_failure'),
    policy_semantic_failure_count: countClassification(required, 'policy_semantic_failure'),
    manual_rerun_required_count: countClassification(required, 'manual_rerun_required'),
    stale_or_superseded_failure_count: sumField(required, 'stale_or_superseded_failure_count'),
    stale_cancelled_count: sumField(required, 'stale_cancelled_count'),
    superseded_count: sumField(required, 'superseded_count'),
    same_head_stale_count: sumField(required, 'same_head_stale_count'),
  };
  expected.operational_failure_count = expected.manual_rerun_required_count;
  expected.semantic_blocking_failure_count = expected.current_required_failure_count + expected.policy_semantic_failure_count;
  expected.operational_note_count = expected.manual_rerun_required_count + expected.stale_or_superseded_failure_count;

  for (const [field, value] of Object.entries(expected)) {
    if (summary[field] !== value) {
      errors.push(createError(
        'required_check_summary_mismatch',
        `${basePath}/${field}`,
        `${field} must equal the required check entry total ${value}, got ${summary[field]}`,
      ));
    }
  }

  const expectedReruns = required.reduce((total, entry) => (
    total + (Number.isInteger(entry?.attempts) ? Math.max(0, entry.attempts - 1) : 0)
  ), 0);
  if (productMetrics?.ci_rerun_count !== expectedReruns) {
    errors.push(createError(
      'ci_rerun_count_mismatch',
      '/agentPrAssurance/productMetrics/ci_rerun_count',
      `ci_rerun_count must equal required check duplicate attempts ${expectedReruns}, got ${productMetrics?.ci_rerun_count}`,
    ));
  }

  const ciRerunClassificationCounts = productMetrics?.ci_rerun_classification_counts;
  if (!isObject(ciRerunClassificationCounts)) {
    errors.push(createError(
      'ci_rerun_classification_counts_mismatch',
      '/agentPrAssurance/productMetrics/ci_rerun_classification_counts',
      `ci_rerun_classification_counts must be collected with required checks, got ${ciRerunClassificationCounts}`,
    ));
  } else {
    const classificationCountsExpected = {
      total: expectedReruns,
      stale_cancelled: expected.stale_cancelled_count,
      superseded: expected.superseded_count,
      same_head_stale: expected.same_head_stale_count,
      manual_rerun_required: expected.manual_rerun_required_count,
    };
    for (const [field, value] of Object.entries(classificationCountsExpected)) {
      if (ciRerunClassificationCounts[field] !== value) {
        errors.push(createError(
          'ci_rerun_classification_counts_mismatch',
          `/agentPrAssurance/productMetrics/ci_rerun_classification_counts/${field}`,
          `${field} must equal ${value}, got ${ciRerunClassificationCounts[field]}`,
        ));
      }
    }
  }

  const regressionSignal = metrics?.agent_regression_signal;
  if (isObject(regressionSignal)) {
    if (regressionSignal.currentFailures !== expected.semantic_blocking_failure_count) {
      errors.push(createError(
        'agent_regression_current_failure_mismatch',
        '/agentPrAssurance/metrics/agent_regression_signal/currentFailures',
        `currentFailures must equal semantic blocking failures ${expected.semantic_blocking_failure_count}, got ${regressionSignal.currentFailures}`,
      ));
    }
    if (regressionSignal.staleOrSupersededFailures !== expected.stale_or_superseded_failure_count) {
      errors.push(createError(
        'agent_regression_stale_failure_mismatch',
        '/agentPrAssurance/metrics/agent_regression_signal/staleOrSupersededFailures',
        `staleOrSupersededFailures must equal stale/superseded failures ${expected.stale_or_superseded_failure_count}, got ${regressionSignal.staleOrSupersededFailures}`,
      ));
    }
    const regressionFieldExpectations = {
      operationalNotes: expected.operational_note_count,
      currentRequiredFailures: expected.current_required_failure_count,
      policySemanticFailures: expected.policy_semantic_failure_count,
      manualRerunRequired: expected.manual_rerun_required_count,
      classificationSource: requiredChecks.source,
    };
    for (const [field, value] of Object.entries(regressionFieldExpectations)) {
      if (regressionSignal[field] !== value) {
        errors.push(createError(
          'agent_regression_classification_mismatch',
          `/agentPrAssurance/metrics/agent_regression_signal/${field}`,
          `${field} must equal ${value}, got ${regressionSignal[field]}`,
        ));
      }
    }
  }
}

export function validateAgenticMetricsSemantics(document) {
  const errors = [];
  const extension = document?.agentPrAssurance;
  if (!isObject(extension)) {
    return errors;
  }
  const metrics = extension.metrics;
  if (!isObject(metrics)) {
    return errors;
  }

  validateClaimCoverage(metrics, errors);
  validateRequiredLaneCompliance(metrics, errors);
  validateEvidenceCompleteness(metrics, errors);
  validateFalseBlockRate(metrics, errors);
  validateRequiredChecks(extension.productMetrics, metrics, errors);

  return errors;
}

export const __testOnly_AGENTIC_METRICS_RATIO_TOLERANCE = RATIO_TOLERANCE;
