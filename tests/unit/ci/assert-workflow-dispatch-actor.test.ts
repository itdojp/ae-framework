import { describe, expect, it } from 'vitest';

import {
  isTrustedPermission,
  parseAllowedPermissions,
  parsePermissionResponse,
} from '../../../scripts/ci/assert-workflow-dispatch-actor.mjs';

describe('assert-workflow-dispatch-actor', () => {
  it('parses allowed permission configuration', () => {
    expect([...parseAllowedPermissions('admin, maintain,write')]).toEqual(['admin', 'maintain', 'write']);
  });

  it('accepts write-like collaborator permissions only', () => {
    const allowed = parseAllowedPermissions('admin,maintain,write');
    expect(isTrustedPermission('admin', allowed)).toBe(true);
    expect(isTrustedPermission('maintain', allowed)).toBe(true);
    expect(isTrustedPermission('write', allowed)).toBe(true);
    expect(isTrustedPermission('triage', allowed)).toBe(false);
    expect(isTrustedPermission('read', allowed)).toBe(false);
  });

  it('parses gh api permission output', () => {
    expect(parsePermissionResponse('write\n')).toBe('write');
    expect(parsePermissionResponse('{"permission":"maintain"}')).toBe('maintain');
  });
});
