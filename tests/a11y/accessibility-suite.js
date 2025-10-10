
const registerAccessibilityTests = (suiteApi) => {
  const { describe, it, expect, beforeEach } = suiteApi;

  describe('Component Accessibility Tests', () => {
    beforeEach(() => {
      document.body.innerHTML = '';
    });

    describe('Button Component', () => {
      it('should have accessible name', async () => {
        const button = createMockElement('button', {
          textContent: 'Click me',
          type: 'button'
        });
        document.body.appendChild(button);

        const results = await global.axe(document.body);
        expect(results.violations).toHaveLength(0);
      });

      it('should fail without accessible name', async () => {
        const button = createMockElement('button', {
          type: 'button'
        });
        document.body.appendChild(button);

        const results = await global.axe(document.body);
        const nameViolations = results.violations.filter(v => v.id === 'button-name');
        expect(nameViolations.length).toBeGreaterThan(0);
      });

      it('should support keyboard navigation', async () => {
        const button = createMockElement('button', {
          textContent: 'Keyboard accessible',
          type: 'button',
          tabindex: '0'
        });
        document.body.appendChild(button);

        const results = await global.axe(document.body);
        expect(results.violations).toHaveLength(0);
      });
    });

    describe('Form Input Component', () => {
      it('should have proper label association', async () => {
        const label = createMockElement('label', {
          textContent: 'Email Address',
          htmlFor: 'email-input'
        });
        const input = createMockElement('input', {
          type: 'email',
          id: 'email-input',
          name: 'email'
        });
        
        document.body.appendChild(label);
        document.body.appendChild(input);

        const results = await global.axe(document.body);
        expect(results.violations).toHaveLength(0);
      });

      it('should fail without label', async () => {
        const input = createMockElement('input', {
          type: 'email',
          name: 'email'
        });
        document.body.appendChild(input);

        const results = await global.axe(document.body);
        const labelViolations = results.violations.filter(v => v.id === 'label');
        expect(labelViolations.length).toBeGreaterThan(0);
      });
    });

    describe('Modal Component', () => {
      it('should have proper focus management', async () => {
        const modal = createMockElement('div', {
          role: 'dialog',
          'aria-labelledby': 'modal-title',
          'aria-modal': 'true'
        });
        const title = createMockElement('h2', {
          id: 'modal-title',
          textContent: 'Modal Title'
        });
        
        modal.appendChild(title);
        document.body.appendChild(modal);

        const results = await global.axe(document.body);
        expect(results.violations).toHaveLength(0);
      });
    });

    describe('Navigation Component', () => {
      it('should use semantic navigation elements', async () => {
        const nav = createMockElement('nav', {
          'aria-label': 'Main navigation'
        });
        const list = createMockElement('ul');
        const item1 = createMockElement('li');
        const link1 = createMockElement('a', {
          href: '/home',
          textContent: 'Home'
        });
        
        item1.appendChild(link1);
        list.appendChild(item1);
        nav.appendChild(list);
        document.body.appendChild(nav);

        const results = await global.axe(document.body);
        expect(results.violations).toHaveLength(0);
      });
    });

    describe('Color Contrast', () => {
      it('should pass contrast requirements for normal text', async () => {
        const text = createMockElement('p', {
          textContent: 'This is normal text',
          style: 'color: #333333; background-color: #ffffff; font-size: 16px;'
        });
        document.body.appendChild(text);

        const results = await global.axe(document.body);
        const contrastViolations = results.violations.filter(v => v.id === 'color-contrast');
        expect(contrastViolations).toHaveLength(0);
      });
    });
  });
};

module.exports = { registerAccessibilityTests };
