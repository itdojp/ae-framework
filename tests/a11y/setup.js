let cachedExpect = typeof globalThis.expect === 'function' ? globalThis.expect : undefined;
let expectExtended = false;

const tryResolveExpect = () => {
  if (!cachedExpect && typeof require === 'function') {
    try {
      ({ expect: cachedExpect } = require('@jest/globals'));
    } catch {
      // ignore
    }
  }

  if (!cachedExpect && typeof require === 'function') {
    try {
      ({ expect: cachedExpect } = require('vitest'));
    } catch {
      // ignore
    }
  }

  return cachedExpect ?? globalThis.expect;
};

const registerMatcher = (instance) => {
  if (!expectExtended && typeof instance?.extend === 'function') {
    instance.extend({
      toHaveNoViolations: async received => {
        const results = await global.axe(received);
        return {
          pass: results.violations.length === 0,
          message: () => results.violations.length > 0
            ? `Found ${results.violations.length} accessibility violations`
            : 'No accessibility violations found'
        };
      }
    });
    expectExtended = true;
  }
};

const ensureExpectExtended = () => {
  const instance = tryResolveExpect();
  if (typeof instance === 'function') {
    registerMatcher(instance);
    cachedExpect = instance;
  }
};

/**
 * Accessibility test setup for Phase 6 Quality Gates
 * Simplified version for Node.js environment
 */

// Mock document object for Node.js environment with minimal tree support
const createBody = () => {
  const body = {
    _innerHTML: '',
    children: [],
    appendChild(node) {
      this.children.push(node);
    }
  };

  Object.defineProperty(body, 'innerHTML', {
    get() {
      return this._innerHTML;
    },
    set(value) {
      this._innerHTML = value;
      this.children = [];
    }
  });

  return body;
};

const body = createBody();

// For now, provide basic test utilities without DOM dependencies
global.createMockElement = (type, initialProps = {}) => {
  const props = { ...initialProps };
  const node = {
    type,
    props,
    children: [],
    appendChild(child) {
      this.children.push(child);
    },
    setAttribute(name, value) {
      props[name] = value;
    },
    getAttribute(name) {
      return props[name];
    }
  };

  let textContent = props.textContent || '';
  Object.defineProperty(node, 'textContent', {
    get() {
      return textContent;
    },
    set(value) {
      textContent = value;
      props.textContent = value;
    }
  });

  return node;
};

global.document = {
  body,
  createElement: (type) => global.createMockElement(type)
};

const collectNodes = (root) => {
  const nodes = [];
  const traverse = (node) => {
    if (!node) return;
    nodes.push(node);
    if (Array.isArray(node.children)) {
      for (const child of node.children) {
        traverse(child);
      }
    }
  };
  traverse(root);
  return nodes;
};

// Mock axe function with simple heuristics for tests
global.axe = async (element) => {
  const nodes = collectNodes(element);
  const violations = [];

  const buttons = nodes.filter((node) => node.type === 'button');
  for (const button of buttons) {
    const name = (button.textContent || '').trim() || button.props['aria-label'] || button.props['aria-labelledby'];
    if (!name) {
      violations.push({
        id: 'button-name',
        impact: 'serious',
        nodes: [button],
        help: 'Buttons must have discernible text'
      });
    }
  }

  const labels = nodes.filter((node) => node.type === 'label');
  const labelledIds = new Set(labels.map((label) => label.props.htmlFor || label.props.for));
  const inputs = nodes.filter((node) => node.type === 'input');

  for (const input of inputs) {
    const id = input.props.id || input.props.name;
    if (!id || !labelledIds.has(id)) {
      violations.push({
        id: 'label',
        impact: 'moderate',
        nodes: [input],
        help: 'Form inputs must have associated labels'
      });
    }
  }

  return { violations };
};

ensureExpectExtended();

console.log('✅ Accessibility test setup completed (Node.js mode)');
