function createError(keyword, instancePath, message) {
  return { keyword, instancePath, message };
}

function hasNonEmptyString(value) {
  return typeof value === 'string' && value.trim().length > 0;
}

function requireFields(value, fields, instancePath, errors) {
  for (const field of fields) {
    if (!hasNonEmptyString(value?.[field])) {
      errors.push(createError(
        'live_evidence_required',
        `${instancePath}/${field}`,
        `live state requires ${field}`,
      ));
    }
  }
}

function validateStateBoundary(surface, instancePath, errors) {
  const blockers = Array.isArray(surface?.blockers) ? surface.blockers : [];
  if (surface?.state === 'blocked' && blockers.length === 0) {
    errors.push(createError(
      'blocked_state_requires_blocker',
      `${instancePath}/blockers`,
      'blocked state requires at least one blocker',
    ));
  }
  if (surface?.state === 'live' && blockers.length > 0) {
    errors.push(createError(
      'live_state_has_blockers',
      `${instancePath}/blockers`,
      'live state cannot retain blockers',
    ));
  }
}

function validateEvidenceTimestamp(manifestAsOf, evidence, instancePath, errors) {
  const timestamp = evidence?.observedAt ?? evidence?.verifiedAt;
  if (!hasNonEmptyString(timestamp) || !hasNonEmptyString(manifestAsOf)) {
    return;
  }
  if (Date.parse(timestamp) > Date.parse(manifestAsOf)) {
    errors.push(createError(
      'evidence_after_manifest',
      `${instancePath}/${evidence.observedAt ? 'observedAt' : 'verifiedAt'}`,
      'evidence timestamp cannot be later than manifest asOf',
    ));
  }
}

function validateBranchProtection(surface, manifestAsOf, errors) {
  const instancePath = '/surfaces/mainBranchProtection';
  validateStateBoundary(surface, instancePath, errors);
  validateEvidenceTimestamp(manifestAsOf, surface?.evidence, `${instancePath}/evidence`, errors);
  if (surface?.state !== 'live') {
    return;
  }

  const evidence = surface.evidence;
  requireFields(
    evidence,
    ['observedAt', 'verifier', 'fetchUrl', 'fetchStatus', 'applyWorkflowRunUrl', 'applyStatus'],
    `${instancePath}/evidence`,
    errors,
  );
  if (evidence?.fetchStatus !== 'success') {
    errors.push(createError(
      'live_fetch_must_succeed',
      `${instancePath}/evidence/fetchStatus`,
      'live branch protection requires successful fetch evidence',
    ));
  }
  if (evidence?.applyStatus !== 'success') {
    errors.push(createError(
      'live_apply_must_succeed',
      `${instancePath}/evidence/applyStatus`,
      'live branch protection requires a successful apply workflow run',
    ));
  }
  const observedContexts = new Set(evidence?.observedContexts ?? []);
  for (const context of surface?.desiredContexts ?? []) {
    if (!observedContexts.has(context)) {
      errors.push(createError(
        'live_context_not_observed',
        `${instancePath}/evidence/observedContexts`,
        `live branch protection is missing observed required context '${context}'`,
      ));
    }
  }
}

function validateNpmCore(surface, manifestAsOf, errors) {
  const instancePath = '/surfaces/coreNpmPackage';
  validateStateBoundary(surface, instancePath, errors);
  validateEvidenceTimestamp(manifestAsOf, surface?.evidence, `${instancePath}/evidence`, errors);
  if (surface?.state !== 'live') {
    return;
  }

  const evidence = surface.evidence;
  requireFields(
    evidence,
    [
      'verifiedAt',
      'verifier',
      'registryUrl',
      'registryVersion',
      'publishWorkflowRunUrl',
      'publishWorkflowMode',
      'publishWorkflowStatus',
      'provenanceUrl',
      'cleanInstallImportEvidenceUrl',
    ],
    `${instancePath}/evidence`,
    errors,
  );
  if (evidence?.publishWorkflowStatus !== 'success') {
    errors.push(createError(
      'live_publish_must_succeed',
      `${instancePath}/evidence/publishWorkflowStatus`,
      'live npm state requires a successful publish workflow run',
    ));
  }
  if (!['bootstrap-token', 'trusted-publisher'].includes(evidence?.publishWorkflowMode)) {
    errors.push(createError(
      'live_publish_mode_invalid',
      `${instancePath}/evidence/publishWorkflowMode`,
      'live npm state requires bootstrap-token or trusted-publisher mode, not preflight',
    ));
  }
  if (evidence?.registryVersion !== surface?.expectedVersion) {
    errors.push(createError(
      'registry_version_mismatch',
      `${instancePath}/evidence/registryVersion`,
      `registryVersion must equal expectedVersion '${surface?.expectedVersion}'`,
    ));
  }
}

function validateMarketplaceAction(surface, manifestAsOf, errors) {
  const instancePath = '/surfaces/assuranceGateMarketplace';
  validateStateBoundary(surface, instancePath, errors);
  validateEvidenceTimestamp(manifestAsOf, surface?.evidence, `${instancePath}/evidence`, errors);
  if (surface?.state !== 'live') {
    return;
  }

  requireFields(
    surface.evidence,
    [
      'verifiedAt',
      'verifier',
      'listingUrl',
      'releaseNoteUrl',
      'externalPathResolutionUrl',
      'externalPathResolutionStatus',
    ],
    `${instancePath}/evidence`,
    errors,
  );
  if (surface?.evidence?.externalPathResolutionStatus !== 'success') {
    errors.push(createError(
      'live_external_path_resolution_must_succeed',
      `${instancePath}/evidence/externalPathResolutionStatus`,
      'live Marketplace state requires successful external action-path resolution evidence',
    ));
  }
}

export function validatePublicationEvidenceSemantics(manifest) {
  const errors = [];
  validateBranchProtection(manifest?.surfaces?.mainBranchProtection, manifest?.asOf, errors);
  validateNpmCore(manifest?.surfaces?.coreNpmPackage, manifest?.asOf, errors);
  validateMarketplaceAction(manifest?.surfaces?.assuranceGateMarketplace, manifest?.asOf, errors);
  return errors;
}
