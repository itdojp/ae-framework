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
  /keine\s+gegenbeispiele/i,             // German: no counterexamples
  /aucun(?:e)?\s+(?:échec|erreurs?)\s+détecté(?:e)?/i, // FR: no failure/error detected
  /no\s+se\s+encontraron\s+(?:errores|violaciones|contraejemplos?)/i, // ES: no errors/violations/counterexamples found
  /keine\s+verletzungen\s+gefunden/i     // DE: no violations found
  ,/keine\s+fehler\s+gefunden/i          // DE: no errors found
  ,/aucune?\s+(?:violation|erreur)s?\s+d[ée]tect[ée]?/i // FR: no violation/error detected
  ,/no\s+se\s+detectaron\s+(?:errores|violaciones|contraejemplos?)/i // ES: no errors/violations/counterexamples detected
];

export const NEGATIVE_PATTERNS = [
  /\bviolation\b/i,
  // Counterexample: require contextual negatives to reduce false positives
  /counter-?examples?\s+(?:found|detected|present|exists?)/i,
  /\bfail(?:ed)?\b/i,
  /\berrors?\s+(?:found|detected)\b/i,
  /error:/i,
  /deadlock\s+(?:found|detected)/i,
  /\bviolat(?:ed|ion)\b/i,
  // Minimal multilingual negatives (conservative)
  /contre[- ]exemples?\s+(?:trouv\w*|détect\w*)/i, // French: counterexample found/detected
  /contraejemplos?\s+(?:encontrad\w*|detectad\w*)/i, // Spanish
  /gegenbeispiele?\s+(?:gefunden|entdeckt)/i,    // German
  // Additional boundaries: explicit failure/violation in FR/ES/DE
  /échec\s+(?:détecté|trouvé)/i,                  // FR failure detected/found
  /violación\s+(?:detectada|encontrada)/i,        // ES violation detected/found
  /fehlers?\s+gefunden/i                          // DE error(s) found
];

export function computeOkFromOutput(out){
  if (!out) return null;
  if (POSITIVE_PATTERNS.some(re => re.test(out))) return true;
  if (NEGATIVE_PATTERNS.some(re => re.test(out))) return false;
  return null;
}
