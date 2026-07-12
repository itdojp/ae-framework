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

function validateBranchProtection(surface, errors) {
  const instancePath = '/surfaces/mainBranchProtection';
  validateStateBoundary(surface, instancePath, errors);
  if (surface?.state !== 'live') {
    return;
  }

  const evidence = surface.evidence;
  requireFields(
    evidence,
    [
      'observedAt',
      'verifier',
      'verifierRole',
      'fetchEndpoint',
      'fetchStatus',
      'applyWorkflowName',
      'applyWorkflowRunUrl',
      'applyStatus',
    ],
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

function validateNpmCore(surface, errors) {
  const instancePath = '/surfaces/coreNpmPackage';
  validateStateBoundary(surface, instancePath, errors);
  if (surface?.state !== 'live') {
    return;
  }

  const evidence = surface.evidence;
  requireFields(
    evidence,
    [
      'verifiedAt',
      'verifier',
      'verifierRole',
      'registryUrl',
      'registryVersion',
      'publishWorkflowName',
      'publishWorkflowFile',
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

function validateMarketplaceAction(surface, errors) {
  const instancePath = '/surfaces/assuranceGateMarketplace';
  validateStateBoundary(surface, instancePath, errors);
  const evidence = surface?.evidence;
  const runtimeSmoke = evidence?.runtimeSmoke;
  const expectedImmutableRef = `itdojp/ae-framework@${surface?.immutableTag}`;
  const expectedMovingRef = `itdojp/ae-framework@${surface?.movingMajorTag}`;
  const expectedReleaseNoteUrl = `https://github.com/itdojp/ae-framework/releases/tag/${surface?.immutableTag}`;
  const expectedActionPathUrl = `https://github.com/itdojp/ae-framework/blob/${surface?.immutableTag}/action.yml`;

  if (surface?.actionRef !== expectedMovingRef) {
    errors.push(createError(
      'marketplace_action_ref_mismatch',
      `${instancePath}/actionRef`,
      `Marketplace actionRef must equal '${expectedMovingRef}'`,
    ));
  }
  if (hasNonEmptyString(evidence?.releaseNoteUrl)
    && evidence.releaseNoteUrl !== expectedReleaseNoteUrl) {
    errors.push(createError(
      'release_note_tag_mismatch',
      `${instancePath}/evidence/releaseNoteUrl`,
      `releaseNoteUrl must reference immutableTag '${surface?.immutableTag}'`,
    ));
  }
  if (hasNonEmptyString(evidence?.externalPathResolutionUrl)
    && evidence.externalPathResolutionUrl !== expectedActionPathUrl) {
    errors.push(createError(
      'external_path_tag_mismatch',
      `${instancePath}/evidence/externalPathResolutionUrl`,
      `externalPathResolutionUrl must reference immutableTag '${surface?.immutableTag}'`,
    ));
  }

  if (runtimeSmoke) {
    const immutable = runtimeSmoke.immutableRelease;
    const moving = runtimeSmoke.movingMajor;
    const immutablePath = `${instancePath}/evidence/runtimeSmoke/immutableRelease`;
    const movingPath = `${instancePath}/evidence/runtimeSmoke/movingMajor`;

    if (immutable?.actionRef !== expectedImmutableRef) {
      errors.push(createError(
        'immutable_action_ref_mismatch',
        `${immutablePath}/actionRef`,
        `immutable runtime actionRef must equal '${expectedImmutableRef}'`,
      ));
    }
    if (moving?.actionRef !== expectedMovingRef) {
      errors.push(createError(
        'moving_action_ref_mismatch',
        `${movingPath}/actionRef`,
        `moving runtime actionRef must equal '${expectedMovingRef}'`,
      ));
    }
    if (immutable?.resolvedCommit !== moving?.resolvedCommit) {
      errors.push(createError(
        'runtime_resolved_commit_mismatch',
        `${movingPath}/resolvedCommit`,
        'immutable release and moving major runtime smoke must resolve to the same commit',
      ));
    }

    const caseLocators = new Set();
    for (const [name, smoke] of [['immutableRelease', immutable], ['movingMajor', moving]]) {
      const smokePath = `${instancePath}/evidence/runtimeSmoke/${name}`;
      const expectedPrefix = `https://github.com/${runtimeSmoke.consumerRepository}/actions/runs/`;
      if (hasNonEmptyString(smoke?.workflowRunUrl)
        && !smoke.workflowRunUrl.startsWith(expectedPrefix)) {
        errors.push(createError(
          'consumer_workflow_url_mismatch',
          `${smokePath}/workflowRunUrl`,
          'workflowRunUrl repository must equal consumerRepository',
        ));
      }
      for (const caseName of ['pass', 'block']) {
        const jobName = smoke?.cases?.[caseName]?.jobName;
        if (!hasNonEmptyString(smoke?.workflowRunUrl) || !hasNonEmptyString(jobName)) {
          continue;
        }
        const locator = `${smoke.workflowRunUrl}#${jobName}`;
        if (caseLocators.has(locator)) {
          errors.push(createError(
            'runtime_case_locator_not_unique',
            `${smokePath}/cases/${caseName}/jobName`,
            'each runtime smoke case must have a unique workflowRunUrl and jobName locator',
          ));
        }
        caseLocators.add(locator);
      }
    }
  }

  if (surface?.state === 'live') {
    requireFields(
      evidence,
      [
        'verifiedAt',
        'verifier',
        'verifierRole',
        'listingUrl',
        'releaseNoteUrl',
        'externalPathResolutionUrl',
        'externalPathResolutionStatus',
      ],
      `${instancePath}/evidence`,
      errors,
    );
    if (!runtimeSmoke) {
      errors.push(createError(
        'live_runtime_smoke_required',
        `${instancePath}/evidence/runtimeSmoke`,
        'live Marketplace state requires immutable release and moving major external runtime smoke evidence',
      ));
    }
    if (evidence?.externalPathResolutionStatus !== 'success') {
      errors.push(createError(
        'live_external_path_resolution_must_succeed',
        `${instancePath}/evidence/externalPathResolutionStatus`,
        'live Marketplace state requires successful external action-path resolution evidence',
      ));
    }
  }
}

export function validatePublicationEvidenceSemantics(manifest) {
  const errors = [];
  validateBranchProtection(manifest?.surfaces?.mainBranchProtection, errors);
  validateNpmCore(manifest?.surfaces?.coreNpmPackage, errors);
  validateMarketplaceAction(manifest?.surfaces?.assuranceGateMarketplace, errors);
  return errors;
}
