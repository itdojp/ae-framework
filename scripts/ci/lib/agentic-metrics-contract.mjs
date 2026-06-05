const RATIO_TOLERANCE = 0.0001;

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

  return errors;
}

export const __testOnly_AGENTIC_METRICS_RATIO_TOLERANCE = RATIO_TOLERANCE;
