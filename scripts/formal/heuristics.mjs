// Shared heuristics for Apalache output classification
export const POSITIVE_PATTERNS = [
  /no\s+(?:errors?|counterexamples?)\s+(?:found|detected|present)\b/i,
  /verification\s+successful/i,
  /\bok\b/i,
  /invariant[^\n]*holds/i,
  /no\s+violations?/i,
  /all\s+propert(?:y|ies)\s+hold/i,
  // Multilingual minimal positives (conservative)
  /aucun\s+contre[- ]exemple/i,           // French: no counterexample
  /sin\s+contraejemplos?/i,              // Spanish: without counterexamples
  /keine\s+gegenbeispiele/i              // German: no counterexamples
];

export const NEGATIVE_PATTERNS = [
  /\bviolation\b/i,
  /counterexample/i,
  /\bfail(?:ed)?\b/i,
  /\berrors?\s+(?:found|detected)\b/i,
  /error:/i,
  // Minimal multilingual negatives (conservative)
  /contre[- ]exemple\s+(?:trouv|detect)/i, // French: counterexample found/detected (prefix match)
  /contraejemplo\s+(?:encontrado|detectado)/i, // Spanish
  /gegenbeispiel\s+(?:gefunden|entdeckt)/i     // German
];

export function computeOkFromOutput(out){
  if (!out) return null;
  if (POSITIVE_PATTERNS.some(re => re.test(out))) return true;
  if (NEGATIVE_PATTERNS.some(re => re.test(out))) return false;
  return null;
}
