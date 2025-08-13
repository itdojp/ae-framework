import { describe, test, expect, beforeEach, afterEach } from '@jest/globals';
import * as fs from 'fs';
import * as path from 'path';
import { SteeringLoader } from '../../src/utils/steering-loader.js';

describe('SteeringLoader', () => {
  const testDir = path.join(process.cwd(), '.test-steering');
  const steeringDir = path.join(testDir, '.ae', 'steering');
  let loader: SteeringLoader;

  beforeEach(async () => {
    // Create test directory structure
    await fs.promises.mkdir(steeringDir, { recursive: true });
    loader = new SteeringLoader(testDir);
  });

  afterEach(async () => {
    // Clean up test directory
    await fs.promises.rm(testDir, { recursive: true, force: true });
  });

  describe('loadDocument', () => {
    test('should load a steering document', async () => {
      const content = '# Product Vision\nTest content';
      await fs.promises.writeFile(path.join(steeringDir, 'product.md'), content);

      const loaded = await loader.loadDocument('product');
      expect(loaded).toBe(content);
    });

    test('should return null for non-existent document', async () => {
      const loaded = await loader.loadDocument('non-existent');
      expect(loaded).toBeNull();
    });

    test('should cache loaded documents', async () => {
      const content = '# Cached Content';
      await fs.promises.writeFile(path.join(steeringDir, 'cached.md'), content);

      const first = await loader.loadDocument('cached');
      const second = await loader.loadDocument('cached');
      
      expect(first).toBe(second);
      expect(first).toBe(content);
    });
  });

  describe('loadCoreDocuments', () => {
    test('should load all core documents', async () => {
      await fs.promises.writeFile(
        path.join(steeringDir, 'product.md'),
        '# Product'
      );
      await fs.promises.writeFile(
        path.join(steeringDir, 'architecture.md'),
        '# Architecture'
      );
      await fs.promises.writeFile(
        path.join(steeringDir, 'standards.md'),
        '# Standards'
      );

      const docs = await loader.loadCoreDocuments();
      
      expect(docs.product).toBe('# Product');
      expect(docs.architecture).toBe('# Architecture');
      expect(docs.standards).toBe('# Standards');
    });

    test('should handle missing core documents', async () => {
      await fs.promises.writeFile(
        path.join(steeringDir, 'product.md'),
        '# Product Only'
      );

      const docs = await loader.loadCoreDocuments();
      
      expect(docs.product).toBe('# Product Only');
      expect(docs.architecture).toBeUndefined();
      expect(docs.standards).toBeUndefined();
    });
  });

  describe('loadCustomDocuments', () => {
    test('should load custom documents', async () => {
      await fs.promises.writeFile(
        path.join(steeringDir, 'custom-api.md'),
        '# API Guidelines'
      );
      await fs.promises.writeFile(
        path.join(steeringDir, 'custom-security.md'),
        '# Security Guidelines'
      );
      await fs.promises.writeFile(
        path.join(steeringDir, 'regular.md'),
        '# Not Custom'
      );

      const docs = await loader.loadCustomDocuments();
      
      expect(docs['custom-api']).toBe('# API Guidelines');
      expect(docs['custom-security']).toBe('# Security Guidelines');
      expect(docs['regular']).toBeUndefined();
    });

    test('should return empty object when no custom documents', async () => {
      const docs = await loader.loadCustomDocuments();
      expect(docs).toEqual({});
    });
  });

  describe('getSteeringContext', () => {
    test('should format steering context for AI agents', async () => {
      await fs.promises.writeFile(
        path.join(steeringDir, 'product.md'),
        '# Product Vision\nBuild great software'
      );
      await fs.promises.writeFile(
        path.join(steeringDir, 'custom-api.md'),
        '# API Standards\nRESTful design'
      );

      const context = await loader.getSteeringContext();
      
      expect(context).toContain('# Project Steering Context');
      expect(context).toContain('## Product Document');
      expect(context).toContain('Build great software');
      expect(context).toContain('## Api Document');
      expect(context).toContain('RESTful design');
    });

    test('should handle no steering documents', async () => {
      const context = await loader.getSteeringContext();
      expect(context).toBe('No steering documents found.');
    });
  });

  describe('hasSteeringDocuments', () => {
    test('should return true when documents exist', async () => {
      await fs.promises.writeFile(
        path.join(steeringDir, 'product.md'),
        'content'
      );

      const hasDocs = await loader.hasSteeringDocuments();
      expect(hasDocs).toBe(true);
    });

    test('should return false when no documents exist', async () => {
      const hasDocs = await loader.hasSteeringDocuments();
      expect(hasDocs).toBe(false);
    });

    test('should return false when directory does not exist', async () => {
      await fs.promises.rm(steeringDir, { recursive: true, force: true });
      
      const hasDocs = await loader.hasSteeringDocuments();
      expect(hasDocs).toBe(false);
    });
  });

  describe('clearCache', () => {
    test('should clear document cache', async () => {
      const content1 = '# Original';
      const content2 = '# Updated';
      const filePath = path.join(steeringDir, 'test.md');

      await fs.promises.writeFile(filePath, content1);
      const first = await loader.loadDocument('test');
      
      await fs.promises.writeFile(filePath, content2);
      const cached = await loader.loadDocument('test');
      
      loader.clearCache();
      const fresh = await loader.loadDocument('test');
      
      expect(first).toBe(content1);
      expect(cached).toBe(content1); // Still cached
      expect(fresh).toBe(content2); // Fresh after cache clear
    });
  });
});