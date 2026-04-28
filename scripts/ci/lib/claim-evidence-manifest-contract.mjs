function createError(keyword, instancePath, message) {
  return { keyword, instancePath, message };
}

function getId(value) {
  return value && typeof value === 'object' && typeof value.id === 'string' ? value.id : null;
}

function validateUniqueIds(items, collectionPath, errors) {
  if (!Array.isArray(items)) {
    return;
  }
  const seen = new Map();
  for (let index = 0; index < items.length; index += 1) {
    const id = getId(items[index]);
    if (!id) {
      continue;
    }
    if (seen.has(id)) {
      errors.push(createError(
        'duplicate_id',
        `/${collectionPath}/${index}/id`,
        `duplicate ${collectionPath} id '${id}' also appears at /${collectionPath}/${seen.get(id)}/id`,
      ));
      continue;
    }
    seen.set(id, index);
  }
}

function validateSourceArtifactReference({
  presentSourceIds,
  absentSourceIds,
  sourceArtifactId,
  instancePath,
  errors,
}) {
  if (sourceArtifactId === undefined || sourceArtifactId === null) {
    return;
  }
  if (typeof sourceArtifactId !== 'string' || sourceArtifactId.length === 0) {
    return;
  }
  if (presentSourceIds.has(sourceArtifactId)) {
    return;
  }
  if (absentSourceIds.has(sourceArtifactId)) {
    errors.push(createError(
      'absent_source_artifact_ref',
      instancePath,
      `sourceArtifactId '${sourceArtifactId}' points to a sourceArtifacts[] entry with present=false`,
    ));
    return;
  }
  errors.push(createError(
    'dangling_source_artifact_ref',
    instancePath,
    `sourceArtifactId '${sourceArtifactId}' does not match any sourceArtifacts[].id`,
  ));
}

function countClaimStatuses(claims) {
  const counts = {
    satisfied: 0,
    partial: 0,
    waived: 0,
    unresolved: 0,
  };
  if (!Array.isArray(claims)) {
    return counts;
  }
  for (const claim of claims) {
    if (!claim || typeof claim !== 'object') {
      continue;
    }
    if (claim.status === 'satisfied') {
      counts.satisfied += 1;
    } else if (claim.status === 'partial') {
      counts.partial += 1;
    } else if (claim.status === 'waived') {
      counts.waived += 1;
    } else if (claim.status === 'unresolved') {
      counts.unresolved += 1;
    }
  }
  return counts;
}

function validateSummary(manifest, errors) {
  const claims = Array.isArray(manifest?.claims) ? manifest.claims : [];
  const summary = manifest?.summary && typeof manifest.summary === 'object' ? manifest.summary : null;
  if (!summary) {
    return;
  }
  const counts = countClaimStatuses(claims);
  const expected = {
    totalClaims: claims.length,
    fullySupported: counts.satisfied,
    partiallySupported: counts.partial,
    waived: counts.waived,
    unresolved: counts.unresolved,
  };
  for (const [field, expectedValue] of Object.entries(expected)) {
    if (summary[field] !== expectedValue) {
      errors.push(createError(
        'summary_mismatch',
        `/summary/${field}`,
        `summary.${field} must be ${expectedValue} based on claims[], got ${summary[field]}`,
      ));
    }
  }
}

function validateClaimReferenceArray({
  claimIndex,
  claim,
  field,
  presentSourceIds,
  absentSourceIds,
  errors,
}) {
  const refs = Array.isArray(claim?.[field]) ? claim[field] : [];
  validateUniqueIds(refs, `claims/${claimIndex}/${field}`, errors);
  for (let refIndex = 0; refIndex < refs.length; refIndex += 1) {
    const ref = refs[refIndex];
    validateSourceArtifactReference({
      presentSourceIds,
      absentSourceIds,
      sourceArtifactId: ref?.sourceArtifactId,
      instancePath: `/claims/${claimIndex}/${field}/${refIndex}/sourceArtifactId`,
      errors,
    });
  }
}

function validateClaimReferences(manifest, errors) {
  const presentSourceIds = new Set();
  const absentSourceIds = new Set();
  if (Array.isArray(manifest?.sourceArtifacts)) {
    for (const sourceArtifact of manifest.sourceArtifacts) {
      const id = getId(sourceArtifact);
      if (!id) {
        continue;
      }
      if (sourceArtifact.present === true) {
        presentSourceIds.add(id);
      } else {
        absentSourceIds.add(id);
      }
    }
  }
  const claims = Array.isArray(manifest?.claims) ? manifest.claims : [];
  const referenceFields = ['evidenceRefs', 'proofObligationRefs', 'missingEvidenceRefs', 'waiverRefs'];
  for (let claimIndex = 0; claimIndex < claims.length; claimIndex += 1) {
    const claim = claims[claimIndex];
    for (const field of referenceFields) {
      validateClaimReferenceArray({
        claimIndex,
        claim,
        field,
        presentSourceIds,
        absentSourceIds,
        errors,
      });
    }
  }
}

function validateWaivedClaimsHaveWaiverRefs(manifest, errors) {
  const claims = Array.isArray(manifest?.claims) ? manifest.claims : [];
  for (let claimIndex = 0; claimIndex < claims.length; claimIndex += 1) {
    const claim = claims[claimIndex];
    if (claim?.status !== 'waived') {
      continue;
    }
    if (!Array.isArray(claim.waiverRefs) || claim.waiverRefs.length === 0) {
      errors.push(createError(
        'waived_claim_missing_waiver',
        `/claims/${claimIndex}/waiverRefs`,
        'waived claims must include at least one waiverRefs entry',
      ));
    }
  }
}

export function validateClaimEvidenceManifestSemantics(manifest) {
  const errors = [];
  validateUniqueIds(manifest?.sourceArtifacts, 'sourceArtifacts', errors);
  validateUniqueIds(manifest?.claims, 'claims', errors);
  validateClaimReferences(manifest, errors);
  validateWaivedClaimsHaveWaiverRefs(manifest, errors);
  validateSummary(manifest, errors);
  return errors;
}
