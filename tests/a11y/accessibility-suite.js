import { createRequire } from 'module';

const require = createRequire(import.meta.url);

const { registerAccessibilityTests } = require('./accessibility-suite.cjs');

export { registerAccessibilityTests };
