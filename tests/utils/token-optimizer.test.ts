import { describe, test, expect, beforeEach } from 'vitest';
import { TokenOptimizer } from '../../src/utils/token-optimizer.js';

describe('TokenOptimizer', () => {
  let optimizer: TokenOptimizer;

  beforeEach(() => {
    optimizer = new TokenOptimizer();
  });

  describe('compressSteeringDocuments', () => {
    test('should compress steering documents', async () => {
      const docs = {
        product: `# Product Vision
          
          This is a comprehensive product vision document with lots of details.
          We have many features planned for this product.
          The product will revolutionize the industry.
          
          ## Target Users
          - Developers
          - Product Managers
          - Designers
          
          ## Core Features
          1. Feature One with detailed explanation
          2. Feature Two with detailed explanation
          3. Feature Three with detailed explanation`,
        
        architecture: `# Architecture
          
          This document describes the system architecture.
          We use microservices architecture.
          The system is built with Node.js and TypeScript.
          
          ## Components
          - API Gateway
          - Service A
          - Service B
          - Database Layer`,
        
        standards: `# Coding Standards
          
          Follow these coding standards.
          Use TypeScript for all code.
          Write tests for everything.
          
          ## Naming Conventions
          - camelCase for functions
          - PascalCase for classes
          - UPPER_CASE for constants`
      };

      const result = await optimizer.compressSteeringDocuments(docs, {
        maxTokens: 1000,
        compressionLevel: 'medium'
      });

      expect(result.compressed).toBeDefined();
      expect(result.stats.compressed).toBeLessThan(result.stats.original);
      expect(result.stats.reductionPercentage).toBeGreaterThan(0);
    });

    test('should respect token limit', async () => {
      const largeDoc = {
        content: 'x'.repeat(10000) // Very large document
      };

      const result = await optimizer.compressSteeringDocuments(largeDoc, {
        maxTokens: 100
      });

      // Estimated tokens should be under limit (with some tolerance)
      expect(result.stats.compressed).toBeLessThanOrEqual(110);
    });

    test('should prioritize documents', async () => {
      const docs = {
        low: 'Low priority content',
        high: 'High priority content',
        medium: 'Medium priority content'
      };

      const result = await optimizer.compressSteeringDocuments(docs, {
        maxTokens: 50,
        preservePriority: ['high', 'medium', 'low']
      });

      // High priority should appear first
      expect(result.compressed.indexOf('HIGH')).toBeLessThan(
        result.compressed.indexOf('MEDIUM')
      );
    });

    test('should use cache for repeated compressions', async () => {
      const docs = {
        test: 'Test document content'
      };

      const options = {
        maxTokens: 100,
        enableCaching: true
      };

      const result1 = await optimizer.compressSteeringDocuments(docs, options);
      const result2 = await optimizer.compressSteeringDocuments(docs, options);

      // Should return same result from cache
      expect(result1.compressed).toBe(result2.compressed);
    });
  });

  describe('optimizeContext', () => {
    test('should optimize context based on relevance', async () => {
      const context = `
        This is about testing.
        This line has nothing important.
        Testing is very important.
        Random content here.
        We need good test coverage.
        Unrelated information.
        Tests should be comprehensive.
      `;

      const result = await optimizer.optimizeContext(
        context,
        100,
        ['test', 'testing']
      );

      expect(result.optimized).toBeDefined();
      expect(result.optimized).toContain('test');
      expect(result.stats.compressed).toBeLessThan(result.stats.original);
    });

    test('should handle code blocks with higher priority', async () => {
      const context = `
        Some text here.
        \`\`\`typescript
        function important() {
          return true;
        }
        \`\`\`
        More text here.
      `;

      const result = await optimizer.optimizeContext(context, 50);
      
      expect(result.optimized).toBeDefined();
      // Code blocks should be preserved when possible
      expect(result.optimized).toContain('```');
    });
  });

  describe('compression levels', () => {
    test('should apply different compression levels', async () => {
      const docs = {
        test: `
          This is a test document.
          This is a test document.
          This is a test document.
          
          // This is a comment
          /* This is a block comment */
          
          Important: This line is important.
          Critical: This line is critical.
          Random text that is not important.
        `
      };

      const lowResult = await optimizer.compressSteeringDocuments(docs, {
        compressionLevel: 'low'
      });

      const highResult = await optimizer.compressSteeringDocuments(docs, {
        compressionLevel: 'high'
      });

      // High compression should result in fewer tokens
      expect(highResult.stats.compressed).toBeLessThan(lowResult.stats.compressed);
      
      // High compression should keep important/critical lines
      expect(highResult.compressed.toLowerCase()).toContain('important');
      expect(highResult.compressed.toLowerCase()).toContain('critical');
    });
  });

  describe('cache management', () => {
    test('should clear cache', () => {
      optimizer.clearCache();
      const stats = optimizer.getCacheStats();
      expect(stats.size).toBe(0);
    });

    test('should report cache statistics', async () => {
      const docs = { test: 'content' };
      
      await optimizer.compressSteeringDocuments(docs, { enableCaching: true });
      
      const stats = optimizer.getCacheStats();
      expect(stats.size).toBe(1);
      expect(stats.maxSize).toBeGreaterThan(0);
    });
  });

  describe('edge cases', () => {
    test('should handle empty documents', async () => {
      const result = await optimizer.compressSteeringDocuments({});
      expect(result.compressed).toBe('');
      expect(result.stats.original).toBe(0);
    });

    test('should handle very small token limits', async () => {
      const docs = {
        test: 'This is a test document with some content'
      };

      const result = await optimizer.compressSteeringDocuments(docs, {
        maxTokens: 10
      });

      expect(result.stats.compressed).toBeLessThanOrEqual(15); // Small tolerance
    });

    test('should handle documents with only whitespace', async () => {
      const docs = {
        empty: '   \n\n   \t\t   \n   '
      };

      const result = await optimizer.compressSteeringDocuments(docs);
      expect(result.compressed).toContain('EMPTY');
      // Should have minimal content after compression
      expect(result.stats.compressed).toBeLessThan(20);
    });
  });
});