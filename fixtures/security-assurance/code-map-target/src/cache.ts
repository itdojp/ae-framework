export interface VerificationInput {
  userId: string;
  resourceId: string;
  verificationResult: string;
}

export function buildCacheKey(input: VerificationInput): string {
  const attackerControlledFields = [
    input.userId,
    input.resourceId,
    input.verificationResult,
  ];
  return attackerControlledFields.join(':');
}

export function unrelatedHealthCheck(): string {
  return 'ok';
}
