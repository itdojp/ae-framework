import type {
  ApalacheSummary,
  TlcSummary,
  VerificationResult,
  VerifierVerdict
} from './types.js';

function verdictFromApalache(summary: ApalacheSummary): VerifierVerdict {
  if (summary.status === 'timeout') {
    return 'error';
  }
  if (!summary.ran) {
    return summary.status === 'tool_not_available' ? 'not_run' : 'error';
  }
  if (summary.ok === true) return 'satisfied';
  if (summary.ok === false) return 'violated';
  return 'unknown';
}

function verdictFromTlc(summary: TlcSummary): VerifierVerdict {
  if (summary.status === 'timeout') {
    return 'error';
  }
  if (!summary.ran) {
    return summary.status === 'tool_not_available' ? 'not_run' : 'error';
  }
  return 'unknown';
}

export function normalizeApalacheSummary(summary: ApalacheSummary): VerificationResult {
  return {
    backend: 'apalache',
    verdict: verdictFromApalache(summary),
    properties: [],
    counterexamples: [],
    summary
  };
}

export function normalizeTlcSummary(summary: TlcSummary): VerificationResult {
  const backend = summary.engine || 'tlc';
  return {
    backend,
    verdict: verdictFromTlc(summary),
    properties: [],
    counterexamples: [],
    summary
  };
}
