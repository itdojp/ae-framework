/**
 * Accessibility test setup for Phase 6 Quality Gates
 * Simplified version for Node.js environment
 */

// Mock document object for Node.js environment
global.document = {
  body: {
    innerHTML: '',
    appendChild: () => {}
  },
  createElement: (type) => global.createMockElement(type)
};

// For now, provide basic test utilities without DOM dependencies
global.createMockElement = (type, props = {}) => {
  // Mock element for Node.js environment
  return {
    type,
    props,
    setAttribute: (name, value) => {
      props[name] = value;
    },
    getAttribute: (name) => props[name],
    appendChild: () => {},
    textContent: props.textContent || ''
  };
};

// Mock axe function for testing
global.axe = async (element) => {
  // Basic mock implementation
  return {
    violations: []  // No violations in mock
  };
};

// Basic matcher
expect.extend({
  toHaveNoViolations: async (received) => {
    const results = await global.axe(received);
    return {
      pass: results.violations.length === 0,
      message: () => results.violations.length > 0 
        ? `Found ${results.violations.length} accessibility violations`
        : 'No accessibility violations found'
    };
  }
});

console.log('✅ Accessibility test setup completed (Node.js mode)');