// Shared heuristics for Apalache output classification
export const POSITIVE_PATTERNS = [
  /no\s+(?:errors?|counterexamples?)\s+(?:found|detected|present)\b/i,
  /verification\s+successful/i,
  /\bok\b/i,
  /invariant[^\n]*holds/i,
  /no\s+violations?/i,
  /all\s+propert(?:y|ies)\s+hold/i
];

export const NEGATIVE_PATTERNS = [
  /\bviolation\b/i,
  /counterexample/i,
  /\bfail(?:ed)?\b/i,
  /\berrors?\s+(?:found|detected)\b/i,
  /error:/i
];

export function computeOkFromOutput(out){
  if (!out) return null;
  if (POSITIVE_PATTERNS.some(re => re.test(out))) return true;
  if (NEGATIVE_PATTERNS.some(re => re.test(out))) return false;
  return null;
}
