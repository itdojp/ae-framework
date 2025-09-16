// Shared heuristics for Apalache output classification
export const POSITIVE_PATTERNS = [
  /\bno\s+(?:errors?|counterexamples?)\b/i,
  /no\s+counterexamples?\s+found/i,
  /verification\s+successful/i,
  /\bok\b/i,
  /invariant[^\n]*holds/i,
  /no\s+violations?/i,
  /all\s+propert(?:y|ies)\s+hold/i
];

export const NEGATIVE_PATTERNS = [
  /\berror\b/i,
  /violation/i,
  /counterexample/i,
  /\bfail(?:ed)?\b/i
];

export function computeOkFromOutput(out){
  if (!out) return null;
  if (POSITIVE_PATTERNS.some(re => re.test(out))) return true;
  if (NEGATIVE_PATTERNS.some(re => re.test(out))) return false;
  return null;
}

