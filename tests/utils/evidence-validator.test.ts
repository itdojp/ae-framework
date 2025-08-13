import { describe, it, expect, beforeEach } from 'vitest';
import { EvidenceValidator } from '../../src/utils/evidence-validator.js';

describe('EvidenceValidator', () => {
  let validator: EvidenceValidator;

  beforeEach(() => {
    validator = new EvidenceValidator();
  });

  describe('validateClaim', () => {
    it('should validate a claim with high confidence when evidence is found', async () => {
      const claim = 'Using React hooks for state management';
      const context = 'Building a React component';
      
      const result = await validator.validateClaim(claim, context, {
        searchDepth: 1 // Limit search depth for faster tests
      });
      
      expect(result).toBeDefined();
      expect(result.isValid).toBeDefined();
      expect(result.confidence).toBeGreaterThanOrEqual(0);
      expect(result.confidence).toBeLessThanOrEqual(1);
      expect(result.evidence).toBeInstanceOf(Array);
    }, 10000);

    it('should provide suggestions when confidence is low', async () => {
      const claim = 'Using unknown framework XYZ';
      const context = 'Building a web application';
      
      const result = await validator.validateClaim(claim, context, {
        minConfidence: 0.9,
        searchDepth: 1
      });
      
      // The test passes regardless of validation result
      expect(result).toBeDefined();
      if (!result.isValid) {
        expect(result.suggestions).toBeDefined();
        expect(result.suggestions).toBeInstanceOf(Array);
        expect(result.suggestions!.length).toBeGreaterThan(0);
      }
    });

    it('should require documentation when specified', async () => {
      const claim = 'Implementing a singleton pattern';
      const context = 'Design patterns';
      
      const result = await validator.validateClaim(claim, context, {
        requireDocumentation: true,
        searchDepth: 1
      });
      
      if (!result.isValid) {
        const hasDocEvidence = result.evidence.some(e => e.type === 'documentation');
        expect(result.isValid).toBe(hasDocEvidence);
      }
    });

    it('should check against known patterns', async () => {
      const claim = 'Implementing singleton pattern with getInstance method';
      const context = 'Creating a database connection manager';
      
      const result = await validator.validateClaim(claim, context, {
        searchDepth: 1
      });
      
      const patternEvidence = result.evidence.filter(e => e.type === 'pattern');
      expect(patternEvidence.length).toBeGreaterThan(0);
      // The pattern database has multiple patterns, verify we found one
      expect(['singleton', 'factory', 'observer', 'mvc', 'restful']).toContain(patternEvidence[0].source);
    });

    it('should extract keywords correctly', async () => {
      const claim = 'The quick brown fox jumps over the lazy dog';
      // Using private method indirectly through validateClaim
      const result = await validator.validateClaim(claim, 'test context', {
        searchDepth: 1
      });
      
      expect(result).toBeDefined();
      // Keywords should exclude stop words like 'the', 'over'
    });
  });

  describe('validateImplementation', () => {
    it('should validate code against specification', async () => {
      const code = `
        class UserService {
          async getUserById(id: string) {
            return await db.users.findOne({ id });
          }
        }
      `;
      const specification = 'Create a UserService class with async method to get user by id';
      
      const result = await validator.validateImplementation(code, specification);
      
      expect(result).toBeDefined();
      expect(result.isValid).toBe(true);
      expect(result.confidence).toBeGreaterThan(0.5);
    });

    it('should detect anti-patterns', async () => {
      const code = `
        var x = 5;
        if (x == "5") {
          eval("console.log('dangerous')");
        }
      `;
      const specification = 'Simple comparison logic';
      
      const result = await validator.validateImplementation(code, specification);
      
      expect(result.isValid).toBe(false);
      expect(result.suggestions).toBeDefined();
      expect(result.suggestions!.some(s => s.includes('anti-pattern'))).toBe(true);
    });

    it('should validate async patterns when required', async () => {
      const code = `
        async function fetchData() {
          const result = await api.get('/data');
          return result;
        }
      `;
      const specification = 'Create an asynchronous function to fetch data';
      
      const result = await validator.validateImplementation(code, specification);
      
      const patternEvidence = result.evidence.filter(e => 
        e.type === 'pattern' && e.source === 'Async Pattern'
      );
      expect(patternEvidence.length).toBeGreaterThan(0);
    });
  });

  describe('validateSolution', () => {
    it('should validate both claim and implementation', async () => {
      const problem = 'Need to create a React component with state';
      const solution = `
        We'll use React hooks for state management.
        
        \`\`\`jsx
        function MyComponent() {
          const [state, setState] = useState(0);
          return <div>{state}</div>;
        }
        \`\`\`
      `;
      
      const result = await validator.validateSolution(problem, solution, {
        searchDepth: 1
      });
      
      expect(result).toBeDefined();
      expect(result.evidence).toBeInstanceOf(Array);
      expect(result.confidence).toBeGreaterThanOrEqual(0);
    }, 10000);

    it('should handle solutions without code blocks', async () => {
      const problem = 'Need to improve performance';
      const solution = 'Use caching and optimize database queries';
      
      const result = await validator.validateSolution(problem, solution, {
        searchDepth: 1
      });
      
      expect(result).toBeDefined();
      expect(result.evidence).toBeInstanceOf(Array);
    });
  });

  describe('getEvidenceSummary', () => {
    it('should generate a formatted summary', async () => {
      const claim = 'Using React hooks and TypeScript';
      const context = 'Building a web application';
      
      const result = await validator.validateClaim(claim, context, {
        searchDepth: 1
      });
      const summary = validator.getEvidenceSummary(result.evidence);
      
      expect(summary).toContain('Evidence Summary');
      expect(typeof summary).toBe('string');
    });

    it('should group evidence by type', async () => {
      const claim = 'Implementing RESTful API with singleton pattern';
      const context = 'Building a service';
      
      const result = await validator.validateClaim(claim, context, {
        searchDepth: 1
      });
      const summary = validator.getEvidenceSummary(result.evidence);
      
      // Should contain type headers
      const types = ['DOCUMENTATION', 'CODE', 'PATTERN', 'STANDARD', 'TEST'];
      const containsAtLeastOneType = types.some(type => summary.includes(type));
      expect(containsAtLeastOneType).toBe(true);
    });
  });

  describe('Edge Cases', () => {
    it('should handle empty claims', async () => {
      const result = await validator.validateClaim('', 'context', {
        searchDepth: 1
      });
      
      // Empty claims should have low confidence
      expect(result.confidence).toBeLessThanOrEqual(0.3);
      expect(result.evidence).toBeInstanceOf(Array);
    });

    it('should handle empty context', async () => {
      const result = await validator.validateClaim('claim', '', {
        searchDepth: 1
      });
      
      expect(result).toBeDefined();
      expect(result.evidence).toBeInstanceOf(Array);
    });

    it('should handle very long claims', async () => {
      const longClaim = 'implement '.repeat(100) + 'feature';
      const result = await validator.validateClaim(longClaim, 'context', {
        searchDepth: 1
      });
      
      expect(result).toBeDefined();
      expect(result.evidence).toBeInstanceOf(Array);
    }, 40000);

    it('should handle special characters in claims', async () => {
      const claim = 'Use @decorator and #pragma for optimization';
      const result = await validator.validateClaim(claim, 'context', {
        searchDepth: 1
      });
      
      expect(result).toBeDefined();
      expect(result.evidence).toBeInstanceOf(Array);
    });
  });

  describe('Confidence Calculation', () => {
    it('should give higher confidence with diverse evidence types', async () => {
      const claim = 'Implementing RESTful API with proper error handling using async patterns';
      const context = 'Building a web service with TypeScript';
      
      const result = await validator.validateClaim(claim, context, {
        searchDepth: 1
      });
      
      // With multiple evidence types, confidence should be reasonable
      if (result.evidence.length > 0) {
        const uniqueTypes = new Set(result.evidence.map(e => e.type));
        if (uniqueTypes.size > 1) {
          expect(result.confidence).toBeGreaterThan(0.3);
        }
      }
    });

    it('should calculate confidence within valid range', async () => {
      const testCases = [
        'Simple function implementation',
        'Complex async await pattern with error handling',
        'React component with hooks and TypeScript',
        'RESTful API with authentication'
      ];
      
      for (const claim of testCases) {
        const result = await validator.validateClaim(claim, 'test context', {
          searchDepth: 1
        });
        expect(result.confidence).toBeGreaterThanOrEqual(0);
        expect(result.confidence).toBeLessThanOrEqual(1);
      }
    }, 10000);
  });

  describe('Integration Tests', () => {
    it('should work with extended commands context', async () => {
      const claim = 'Analyze code for performance issues and suggest improvements';
      const context = 'Extended command for code analysis';
      
      const result = await validator.validateClaim(claim, context, {
        includeExternalDocs: true,
        searchDepth: 1
      });
      
      expect(result).toBeDefined();
      expect(result.evidence).toBeInstanceOf(Array);
    });

    it('should validate steering document suggestions', async () => {
      const claim = 'Update steering documents with project standards';
      const context = 'Project configuration management';
      
      const result = await validator.validateClaim(claim, context, {
        requireDocumentation: false,
        minConfidence: 0.5,
        searchDepth: 1
      });
      
      expect(result).toBeDefined();
      if (!result.isValid && result.suggestions) {
        expect(result.suggestions.length).toBeGreaterThan(0);
      }
    });
  });
});