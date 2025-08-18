/**
 * Accessibility test setup for Phase 6 Quality Gates
 * Configures axe-core and testing utilities
 */

import { configureAxe } from 'jest-axe';
import 'jest-dom/extend-expect';

// Configure axe-core for WCAG 2.1 AA compliance
const axe = configureAxe({
  rules: {
    // Enable WCAG 2.1 AA rules
    'color-contrast': { enabled: true },
    'focus-order-semantics': { enabled: true },
    'keyboard': { enabled: true },
    'aria-allowed-attr': { enabled: true },
    'aria-required-attr': { enabled: true },
    'aria-valid-attr-value': { enabled: true },
    'aria-valid-attr': { enabled: true },
    'label': { enabled: true },
    'form-field-multiple-labels': { enabled: true }
  },
  tags: ['wcag2a', 'wcag2aa', 'wcag21aa']
});

// Add axe to global scope for tests
global.axe = axe;

// Custom matcher for accessibility violations
expect.extend({
  toHaveNoViolations: async (received) => {
    const results = await axe(received);
    const violations = results.violations;
    
    if (violations.length === 0) {
      return {
        pass: true,
        message: () => 'Expected element to have accessibility violations, but none were found'
      };
    }
    
    const violationMessages = violations.map(violation => 
      `${violation.id}: ${violation.description}\n` +
      violation.nodes.map(node => `  - ${node.target.join(', ')}: ${node.failureSummary}`).join('\n')
    ).join('\n\n');
    
    return {
      pass: false,
      message: () => `Expected no accessibility violations, but found:\n\n${violationMessages}`
    };
  }
});

// Global test utilities
global.createMockElement = (type, props = {}) => {
  const element = document.createElement(type);
  Object.keys(props).forEach(key => {
    if (key.startsWith('aria-') || key === 'role' || key === 'tabindex') {
      element.setAttribute(key, props[key]);
    } else {
      element[key] = props[key];
    }
  });
  return element;
};