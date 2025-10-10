import { describe, it, expect, beforeEach } from 'vitest';
import { registerAccessibilityTests } from './accessibility-suite.js';

describe('Accessibility (Vitest)', () => {
  registerAccessibilityTests({ describe, it, expect, beforeEach });
});
