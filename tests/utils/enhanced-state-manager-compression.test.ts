import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { EnhancedStateManager } from '../../src/utils/enhanced-state-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';

describe('EnhancedStateManager Compression Fix', () => {
  let stateManager: EnhancedStateManager;
  const testDataDir = path.join(process.cwd(), 'test-data-compression');

  beforeEach(async () => {
    // Create test data directory
    await fs.mkdir(testDataDir, { recursive: true });
    
    stateManager = new EnhancedStateManager(testDataDir, {
      compressionThreshold: 10, // Very low threshold to trigger compression
      enableTransactions: false
    });
  });

  afterEach(async () => {
    // Clean up test data
    try {
      await fs.rm(testDataDir, { recursive: true });
    } catch (error) {
      // Ignore cleanup errors
    }
  });

  it('should handle compression without TypeScript errors', async () => {
    // Create data large enough to trigger compression
    const largeData = {
      id: 'test-large-data',
      name: 'Large Test Data',
      type: 'test',
      version: '1.0.0',
      content: 'A'.repeat(100) // Large content to trigger compression
    };

    // Save the data - this should trigger compression internally
    const savedKey = await stateManager.saveSSOT('test-compression', largeData);
    
    expect(savedKey).toBeDefined();
    expect(typeof savedKey).toBe('string');

    // Load the data back - this should decompress it
    const loadedData = await stateManager.loadSSOT('test-compression');
    
    expect(loadedData).toBeDefined();
    expect(loadedData.id).toBe(largeData.id);
    expect(loadedData.name).toBe(largeData.name);
    expect(loadedData.content).toBe(largeData.content);
  });

  it('should handle small data without compression', async () => {
    // Create small data that won't trigger compression
    const smallData = {
      id: 'small',
      name: 'Small',
      type: 'test'
    };

    // Save and load small data
    const savedKey = await stateManager.saveSSOT('test-small', smallData);
    const loadedData = await stateManager.loadSSOT('test-small');
    
    expect(loadedData).toEqual(smallData);
  });
});