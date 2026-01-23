import { describe, it, expect } from 'vitest';
import { normalizeApalacheSummary, normalizeTlcSummary } from '../../src/verifier-adapter/normalize.js';
import type { ApalacheSummary, TlcSummary } from '../../src/verifier-adapter/types.js';

describe('verifier-adapter summary normalization', () => {
  it('maps apalache ok=true to satisfied', () => {
    const summary: ApalacheSummary = {
      tool: 'apalache',
      file: 'spec/tla/DomainSpec.tla',
      ran: true,
      status: 'ran',
      ok: true
    };
    const result = normalizeApalacheSummary(summary);
    expect(result.verdict).toBe('satisfied');
    expect(result.backend).toBe('apalache');
  });

  it('maps apalache ok=false to violated', () => {
    const summary: ApalacheSummary = {
      tool: 'apalache',
      file: 'spec/tla/DomainSpec.tla',
      ran: true,
      status: 'ran',
      ok: false
    };
    const result = normalizeApalacheSummary(summary);
    expect(result.verdict).toBe('violated');
  });

  it('maps apalache not-run to not_run', () => {
    const summary: ApalacheSummary = {
      tool: 'apalache',
      file: 'spec/tla/DomainSpec.tla',
      ran: false,
      status: 'tool_not_available',
      ok: null
    };
    const result = normalizeApalacheSummary(summary);
    expect(result.verdict).toBe('not_run');
  });

  it('maps apalache timeout to error', () => {
    const summary: ApalacheSummary = {
      tool: 'apalache',
      file: 'spec/tla/DomainSpec.tla',
      ran: false,
      status: 'timeout',
      ok: null
    };
    const result = normalizeApalacheSummary(summary);
    expect(result.verdict).toBe('error');
  });

  it('maps tlc ran to unknown', () => {
    const summary: TlcSummary = {
      engine: 'tlc',
      file: 'spec/tla/DomainSpec.tla',
      ran: true,
      status: 'ran'
    };
    const result = normalizeTlcSummary(summary);
    expect(result.verdict).toBe('unknown');
    expect(result.backend).toBe('tlc');
  });

  it('maps tlc timeout to error', () => {
    const summary: TlcSummary = {
      engine: 'tlc',
      file: 'spec/tla/DomainSpec.tla',
      ran: false,
      status: 'timeout'
    };
    const result = normalizeTlcSummary(summary);
    expect(result.verdict).toBe('error');
  });
});
