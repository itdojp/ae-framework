export function buildFixtureCacheKey(tenantId: string, subjectId: string): string {
  return `fixture:${tenantId}:${subjectId}`;
}
