const { registerAccessibilityTests } = require('./accessibility-suite.js');
const { describe, it, expect, beforeEach } = require('@jest/globals');

describe('Accessibility (Jest)', () => {
  registerAccessibilityTests({ describe, it, expect, beforeEach });
});
