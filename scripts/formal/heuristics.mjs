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
  ,/all\s+invariants?\s+(?:satisfied|hold)/i
  ,/no\s+property\s+violations?\b/i
  ,/no\s+counterexample\s+found\s+in\s+\d+\s+steps?/i
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
  ,/invariant\s+(?:violated|verlet[zt]t)/i        // EN/DE invariant violated
  ,/propri[ée]t[ée]\s+viol[ée]e/i                // FR property violated
  ,/propiedad\s+violada/i                         // ES property violated
  ,/counter-?example\s+(?:produced|generated)/i   // EN counterexample produced
  ,/propert(?:y|ies)\s+(?:do(?:es)?\s+not|doesn't)\s+hold/i // EN property does not hold
  ,/la\s+propiedad\s+no\s+se\s+cumple/i         // ES property does not hold
  ,/die\s+eigenschaft\s+gilt\s+nicht/i          // DE property does not hold
  ,/la\s+propri[ée]t[ée]\s+ne\s+tient\s+pas/i  // FR property does not hold
  ,/assertion\s+failed/i                          // EN assertion failed
  ,/unsatisfied\s+(?:invariant|property|spec)/i   // EN unsatisfied invariant/property/spec
  ,/(?:invariant|property|spec)\s+unsatisfied/i   // EN <kind> unsatisfied
];

export const CAUTION_PATTERNS = [
  /caution/i,
  /attention[:\s]/i,           // EN/FR-like "attention:"
  /achtung[:\s]/i,             // DE "Achtung:"
  /precaución[:\s]/i,          // ES "Precaución:"
  /atención[:\s]/i,            // ES "Atención:"
  /cuidado[:\s]/i,             // ES "Cuidado:"
  /advertencia[:\s]/i,         // ES "Advertencia:"
  /aviso[:\s]/i,               // ES "Aviso:"
  /warning[:\s]/i,             // EN "Warning:"
  /note[:\s]/i,                // EN "Note:"
  /notice[:\s]/i,              // EN "Notice:"
  /caveat[:\s]/i,              // EN "Caveat:"
  /disclaimer[:\s]/i,          // EN "Disclaimer:"
  /\bN\.?B\.?[:\s]/i,          // EN "NB:" / "N.B.:"
  /hinweis[:\s]/i,             // DE "Hinweis:"
  /warnung[:\s]/i,             // DE "Warnung:"
  /vorsicht[:\s]/i,            // DE "Vorsicht:"
  /remarque[:\s]/i,            // FR "Remarque:"
  /avertissement[:\s]/i,       // FR "Avertissement:"
  /nota[:\s]/i,                // ES "Nota:"
  /heads?\s*up[:\s]/i,         // EN "Heads up:"
  /psa[:\s]/i,                 // EN "PSA:"
  /注意[:：]/,                    // JA "注意:" / 全角コロン対応
  /ご注意/ ,                      // JA "ご注意"
  /警告[:：]?/ ,                  // JA "警告:"（コロン有無）
  /備考[:：]/,                    // JA "備考:" / 全角コロン対応
  /留意点/ ,                    // JA "留意点"
  /注意点/ ,                    // JA "注意点"
  /重要[:：]/ ,                  // JA "重要:" / 全角コロン対応
  /注記[:：]?/ ,                 // JA "注記:"（コロン有無）
  /補足[:：]?/ ,                 // JA "補足:"（コロン有無）
  /注意喚起/ ,                  // JA "注意喚起"
  /注意事項/ ,                  // JA "注意事項"
  /注意/                        // JA "注意"
];

export function computeOkFromOutput(out){
  if (!out) return null;
  if (POSITIVE_PATTERNS.some(re => re.test(out))) return true;
  if (NEGATIVE_PATTERNS.some(re => re.test(out))) return false;
  return null;
}
