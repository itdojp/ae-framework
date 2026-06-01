import { describe, expect, it } from 'vitest';

const policyModule = () => import('../../../scripts/trace/outbound-url-policy.mjs');

describe('outbound URL policy', () => {
  it('allows localhost HTTP only for explicit development exceptions', async () => {
    const { validateTokenBearingUrl } = await policyModule();

    const parsed = validateTokenBearingUrl('http://localhost:3000', {
      serviceName: 'Grafana',
      allowLocalhostHttp: true,
    });

    expect(parsed.origin).toBe('http://localhost:3000');

    const ipv6 = validateTokenBearingUrl('http://[::1]:3000', {
      serviceName: 'Grafana',
      allowLocalhostHttp: true,
    });
    expect(ipv6.origin).toBe('http://[::1]:3000');
  });

  it('requires HTTPS for remote token-bearing destinations', async () => {
    const { validateTokenBearingUrl } = await policyModule();

    expect(() => validateTokenBearingUrl('http://grafana.example.com', {
      serviceName: 'Grafana',
      allowedHosts: new Set(['grafana.example.com']),
      allowLocalhostHttp: true,
    })).toThrow(/must use HTTPS/);
  });

  it('does not read an accidental process.env.undefined allowlist', async () => {
    const { validateTokenBearingUrl } = await policyModule();
    const previous = process.env.undefined;
    process.env.undefined = 'grafana.example.com';
    try {
      expect(() => validateTokenBearingUrl('https://grafana.example.com', {
        serviceName: 'Grafana',
      })).toThrow(/host must be explicitly allowlisted/);
    } finally {
      if (previous === undefined) {
        delete process.env.undefined;
      } else {
        process.env.undefined = previous;
      }
    }
  });

  it('requires explicit host allowlisting for remote HTTPS destinations', async () => {
    const { validateTokenBearingUrl } = await policyModule();

    expect(() => validateTokenBearingUrl('https://grafana.example.com', {
      serviceName: 'Grafana',
      allowedHosts: new Set(['other.example.com']),
      allowLocalhostHttp: true,
    })).toThrow(/host must be explicitly allowlisted/);

    expect(validateTokenBearingUrl('https://grafana.example.com', {
      serviceName: 'Grafana',
      allowedHosts: new Set(['grafana.example.com']),
      allowLocalhostHttp: true,
    }).origin).toBe('https://grafana.example.com');
  });

  it('rejects userinfo before token-bearing requests are built', async () => {
    const { validateTokenBearingUrl } = await policyModule();

    expect(() => validateTokenBearingUrl('https://user:pass@grafana.example.com', {
      serviceName: 'Grafana',
      allowedHosts: new Set(['grafana.example.com']),
      allowLocalhostHttp: true,
    })).toThrow(/must not contain userinfo/);
  });

  it('redacts and bounds external response text', async () => {
    const { sanitizeExternalResponseText } = await policyModule();

    const sanitized = sanitizeExternalResponseText('Authorization=Bearer abc token=secret-value ' + 'x'.repeat(100), 80);

    expect(sanitized).toContain('token=[REDACTED]');
    expect(sanitized).not.toContain('secret-value');
    expect(sanitized).toContain('[truncated]');
  });
});
