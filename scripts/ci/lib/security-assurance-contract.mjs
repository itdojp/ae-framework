function createError(keyword, instancePath, message) {
  return { keyword, instancePath, message };
}

function validateAffectedLocationRanges(findingsDocument, errors) {
  const findings = Array.isArray(findingsDocument?.findings) ? findingsDocument.findings : [];
  for (let findingIndex = 0; findingIndex < findings.length; findingIndex += 1) {
    const finding = findings[findingIndex];
    const locations = Array.isArray(finding?.affectedLocations) ? finding.affectedLocations : [];
    for (let locationIndex = 0; locationIndex < locations.length; locationIndex += 1) {
      const location = locations[locationIndex];
      if (!Number.isInteger(location?.startLine) || !Number.isInteger(location?.endLine)) {
        continue;
      }
      if (location.endLine < location.startLine) {
        errors.push(createError(
          'line_range_order',
          `/findings/${findingIndex}/affectedLocations/${locationIndex}/endLine`,
          `endLine must be greater than or equal to startLine (${location.startLine}), got ${location.endLine}`,
        ));
      }
    }
  }
}

function validateCodeMapLocationRanges(codeMapDocument, errors) {
  const mappings = Array.isArray(codeMapDocument?.mappings) ? codeMapDocument.mappings : [];
  for (let mappingIndex = 0; mappingIndex < mappings.length; mappingIndex += 1) {
    const mapping = mappings[mappingIndex];
    const locations = Array.isArray(mapping?.candidateLocations) ? mapping.candidateLocations : [];
    for (let locationIndex = 0; locationIndex < locations.length; locationIndex += 1) {
      const location = locations[locationIndex];
      if (!Number.isInteger(location?.startLine) || !Number.isInteger(location?.endLine)) {
        continue;
      }
      if (location.endLine < location.startLine) {
        errors.push(createError(
          'line_range_order',
          `/mappings/${mappingIndex}/candidateLocations/${locationIndex}/endLine`,
          `endLine must be greater than or equal to startLine (${location.startLine}), got ${location.endLine}`,
        ));
      }
    }
  }
}


function validateAuditTaskLocationRanges(taskBundleDocument, errors) {
  const tasks = Array.isArray(taskBundleDocument?.tasks) ? taskBundleDocument.tasks : [];
  for (let taskIndex = 0; taskIndex < tasks.length; taskIndex += 1) {
    const task = tasks[taskIndex];
    const locations = Array.isArray(task?.candidateLocations) ? task.candidateLocations : [];
    for (let locationIndex = 0; locationIndex < locations.length; locationIndex += 1) {
      const location = locations[locationIndex];
      if (!Number.isInteger(location?.startLine) || !Number.isInteger(location?.endLine)) {
        continue;
      }
      if (location.endLine < location.startLine) {
        errors.push(createError(
          'line_range_order',
          `/tasks/${taskIndex}/candidateLocations/${locationIndex}/endLine`,
          `endLine must be greater than or equal to startLine (${location.startLine}), got ${location.endLine}`,
        ));
      }
    }
  }
}

function validateReviewRootCauseConsistency(reviewDocument, errors) {
  const unresolvedOrNonFalsePositiveResults = new Set([
    'needs-human-review',
    'confirmed',
    'waived',
  ]);
  const falsePositiveResults = new Set([
    'rejected',
    'out-of-scope',
  ]);
  const reviews = Array.isArray(reviewDocument?.reviews) ? reviewDocument.reviews : [];
  for (let reviewIndex = 0; reviewIndex < reviews.length; reviewIndex += 1) {
    const review = reviews[reviewIndex];
    if (!review || typeof review !== 'object') {
      continue;
    }
    if (unresolvedOrNonFalsePositiveResults.has(review.result) && review.falsePositiveRootCause !== null) {
      errors.push(createError(
        'false_positive_root_cause_result_mismatch',
        `/reviews/${reviewIndex}/falsePositiveRootCause`,
        `falsePositiveRootCause must be null when result is ${review.result}`,
      ));
    }
    if (falsePositiveResults.has(review.result) && review.falsePositiveRootCause === null) {
      errors.push(createError(
        'false_positive_root_cause_missing',
        `/reviews/${reviewIndex}/falsePositiveRootCause`,
        `falsePositiveRootCause must be set when result is ${review.result}`,
      ));
    }
  }
}

export function validateSecurityFindingSemantics(findingsDocument) {
  const errors = [];
  validateAffectedLocationRanges(findingsDocument, errors);
  return errors;
}

export function validateSecurityAuditTaskBundleSemantics(taskBundleDocument) {
  const errors = [];
  validateAuditTaskLocationRanges(taskBundleDocument, errors);
  return errors;
}

export function validateSecurityCodeMapSemantics(codeMapDocument) {
  const errors = [];
  validateCodeMapLocationRanges(codeMapDocument, errors);
  return errors;
}

export function validateSecurityReviewSemantics(reviewDocument) {
  const errors = [];
  validateReviewRootCauseConsistency(reviewDocument, errors);
  return errors;
}
