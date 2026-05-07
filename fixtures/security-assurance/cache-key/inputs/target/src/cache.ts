export interface VerificationRequest {
  tenantId: string;
  subjectId: string;
  scope: string;
  tokenId: string;
}

export interface BearerToken {
  tokenId: string;
  expiresAtEpochMs: number;
}

export function buildCacheKey(input: VerificationRequest): string {
  const attackerControlledTenant = input.tenantId.trim().toLowerCase();
  const attackerControlledSubject = input.subjectId.trim().toLowerCase();

  // SECURITY-FIXTURE: intentionally omits attacker-controlled authorization scope.
  return `verification:${attackerControlledTenant}:${attackerControlledSubject}`;
}

export function isFreshToken(token: BearerToken, nowEpochMs: number): boolean {
  return token.expiresAtEpochMs > nowEpochMs;
}

export function lookupVerificationCache(input: VerificationRequest, token: BearerToken, nowEpochMs: number): string | null {
  if (!isFreshToken(token, nowEpochMs)) {
    return null;
  }
  return buildCacheKey(input);
}
