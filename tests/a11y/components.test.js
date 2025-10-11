const { registerAccessibilityTests } = require('./accessibility-suite.cjs');

const isJest = Boolean(
  (typeof process !== 'undefined' && process.env && process.env.JEST_WORKER_ID) ||
  typeof globalThis.jest !== 'undefined'
);

if (!isJest) {
  if (typeof describe === 'function' && typeof describe.skip === 'function') {
    describe.skip('Accessibility (Jest 専用スイート)', () => {
      if (typeof it === 'function') {
        it('is skipped outside Jest', () => {});
      }
    });
  }
} else {
  const { describe, it, expect, beforeEach } = require('@jest/globals');

  describe('Accessibility (Jest)', () => {
    registerAccessibilityTests({ describe, it, expect, beforeEach });
  });
}
