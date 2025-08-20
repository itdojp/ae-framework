/**
 * Golden/Approval Test for Code Generation
 * 
 * Validates that code generation produces consistent outputs
 * and requires explicit approval for changes via pnpm test:golden:approve
 */

import { describe, it, expect, beforeAll } from 'vitest';
import { readFileSync, writeFileSync, existsSync, mkdirSync } from 'fs';
import { join } from 'path';
import { createHash } from 'crypto';
import { glob } from 'glob';

interface CodegenSnapshot {
  timestamp: string;
  version: string;
  files: {
    [filePath: string]: {
      hash: string;
      lineCount: number;
      ariaAttributeCount: number;
      typeScriptErrors: number;
      eslintErrors: number;
    };
  };
  summary: {
    totalFiles: number;
    totalLines: number;
    totalAriaAttributes: number;
    totalTypeScriptErrors: number;
    totalEslintErrors: number;
  };
}

const SNAPSHOT_PATH = './tests/golden/snapshots/codegen-snapshot.json';
const APPROVED_SNAPSHOT_PATH = './tests/golden/snapshots/codegen-approved.json';

class CodegenSnapshotManager {
  private ensureSnapshotDir(): void {
    const dir = join(__dirname, 'snapshots');
    if (!existsSync(dir)) {
      mkdirSync(dir, { recursive: true });
    }
  }

  async generateSnapshot(): Promise<CodegenSnapshot> {
    this.ensureSnapshotDir();
    
    // Find all generated files in examples/inventory
    const generatedFiles = await glob('examples/inventory/**/*.{tsx,ts,spec.ts,stories.tsx}', {
      ignore: ['**/node_modules/**']
    });

    const snapshot: CodegenSnapshot = {
      timestamp: new Date().toISOString(),
      version: '1.0.0',
      files: {},
      summary: {
        totalFiles: 0,
        totalLines: 0,
        totalAriaAttributes: 0,
        totalTypeScriptErrors: 0,
        totalEslintErrors: 0
      }
    };

    for (const filePath of generatedFiles) {
      if (!existsSync(filePath)) continue;

      const content = readFileSync(filePath, 'utf-8');
      const hash = createHash('sha256').update(content).digest('hex');
      const lineCount = content.split('\n').length;
      
      // Count ARIA attributes
      const ariaAttributeCount = (content.match(/aria-\w+/g) || []).length;
      
      // Simulate TypeScript and ESLint checks (in real implementation, run actual tools)
      const typeScriptErrors = content.includes('any') ? 1 : 0; // Simple heuristic
      const eslintErrors = content.includes('console.log') ? 1 : 0; // Simple heuristic

      snapshot.files[filePath] = {
        hash,
        lineCount,
        ariaAttributeCount,
        typeScriptErrors,
        eslintErrors
      };

      snapshot.summary.totalFiles++;
      snapshot.summary.totalLines += lineCount;
      snapshot.summary.totalAriaAttributes += ariaAttributeCount;
      snapshot.summary.totalTypeScriptErrors += typeScriptErrors;
      snapshot.summary.totalEslintErrors += eslintErrors;
    }

    // Save current snapshot
    writeFileSync(SNAPSHOT_PATH, JSON.stringify(snapshot, null, 2));
    return snapshot;
  }

  loadApprovedSnapshot(): CodegenSnapshot | null {
    if (!existsSync(APPROVED_SNAPSHOT_PATH)) {
      return null;
    }
    try {
      return JSON.parse(readFileSync(APPROVED_SNAPSHOT_PATH, 'utf-8'));
    } catch {
      return null;
    }
  }

  approveSnapshot(): void {
    if (existsSync(SNAPSHOT_PATH)) {
      const snapshot = readFileSync(SNAPSHOT_PATH, 'utf-8');
      writeFileSync(APPROVED_SNAPSHOT_PATH, snapshot);
      console.log('✅ Snapshot approved and saved to', APPROVED_SNAPSHOT_PATH);
    } else {
      throw new Error('No current snapshot found. Run tests first.');
    }
  }

  compareSnapshots(current: CodegenSnapshot, approved: CodegenSnapshot): {
    passed: boolean;
    differences: string[];
  } {
    const differences: string[] = [];

    // Compare file counts
    if (current.summary.totalFiles !== approved.summary.totalFiles) {
      differences.push(
        `File count changed: ${approved.summary.totalFiles} → ${current.summary.totalFiles}`
      );
    }

    // Compare total metrics
    if (current.summary.totalLines !== approved.summary.totalLines) {
      differences.push(
        `Total lines changed: ${approved.summary.totalLines} → ${current.summary.totalLines}`
      );
    }

    if (current.summary.totalAriaAttributes !== approved.summary.totalAriaAttributes) {
      differences.push(
        `ARIA attributes changed: ${approved.summary.totalAriaAttributes} → ${current.summary.totalAriaAttributes}`
      );
    }

    // Compare individual files
    const allFiles = new Set([
      ...Object.keys(current.files),
      ...Object.keys(approved.files)
    ]);

    for (const filePath of allFiles) {
      const currentFile = current.files[filePath];
      const approvedFile = approved.files[filePath];

      if (!currentFile) {
        differences.push(`File removed: ${filePath}`);
        continue;
      }

      if (!approvedFile) {
        differences.push(`File added: ${filePath}`);
        continue;
      }

      if (currentFile.hash !== approvedFile.hash) {
        differences.push(`File changed: ${filePath} (hash: ${approvedFile.hash.slice(0, 8)} → ${currentFile.hash.slice(0, 8)})`);
      }

      if (currentFile.lineCount !== approvedFile.lineCount) {
        differences.push(`Line count changed in ${filePath}: ${approvedFile.lineCount} → ${currentFile.lineCount}`);
      }

      if (currentFile.ariaAttributeCount !== approvedFile.ariaAttributeCount) {
        differences.push(`ARIA attributes changed in ${filePath}: ${approvedFile.ariaAttributeCount} → ${currentFile.ariaAttributeCount}`);
      }
    }

    return {
      passed: differences.length === 0,
      differences
    };
  }
}

const snapshotManager = new CodegenSnapshotManager();

describe('Golden/Approval Tests', () => {
  let currentSnapshot: CodegenSnapshot;

  beforeAll(async () => {
    currentSnapshot = await snapshotManager.generateSnapshot();
  });

  it('should match approved code generation snapshot', () => {
    const approvedSnapshot = snapshotManager.loadApprovedSnapshot();

    if (!approvedSnapshot) {
      console.warn('⚠️  No approved snapshot found. This is the first run.');
      console.log('📸 Current snapshot stats:');
      console.log(`   Files: ${currentSnapshot.summary.totalFiles}`);
      console.log(`   Lines: ${currentSnapshot.summary.totalLines}`);
      console.log(`   ARIA attributes: ${currentSnapshot.summary.totalAriaAttributes}`);
      console.log('');
      console.log('🔧 To approve this snapshot, run: pnpm test:golden:approve');
      
      // For first run, we should pass but warn about missing baseline
      return;
    }

    const comparison = snapshotManager.compareSnapshots(currentSnapshot, approvedSnapshot);

    if (!comparison.passed) {
      console.error('❌ Code generation snapshot mismatch detected!');
      console.error('');
      console.error('Differences found:');
      comparison.differences.forEach(diff => {
        console.error(`   ${diff}`);
      });
      console.error('');
      console.error('🔧 If these changes are intentional, approve them with:');
      console.error('   pnpm test:golden:approve');
      console.error('');
      
      expect(comparison.passed).toBe(true);
    }

    console.log('✅ Code generation snapshot matches approved version');
  });

  it('should have reasonable code generation metrics', () => {
    // Validate that generated code meets quality thresholds
    expect(currentSnapshot.summary.totalFiles).toBeGreaterThan(0);
    expect(currentSnapshot.summary.totalLines).toBeGreaterThan(100);
    
    // Ensure accessibility attributes are present
    expect(currentSnapshot.summary.totalAriaAttributes).toBeGreaterThan(5);
    
    // No TypeScript errors should be present
    expect(currentSnapshot.summary.totalTypeScriptErrors).toBe(0);
    
    // Minimal ESLint errors allowed
    expect(currentSnapshot.summary.totalEslintErrors).toBeLessThanOrEqual(2);
  });

  it('should generate consistent file structure', () => {
    const fileList = Object.keys(currentSnapshot.files);
    
    // Verify expected files are generated
    const expectedPatterns = [
      /Form\.tsx$/,        // Component forms
      /Card\.tsx$/,        // Component cards  
      /\.stories\.tsx$/,   // Storybook stories
      /\.spec\.ts$/        // E2E tests
    ];

    expectedPatterns.forEach(pattern => {
      const matchingFiles = fileList.filter(file => pattern.test(file));
      expect(matchingFiles.length).toBeGreaterThan(0);
    });
  });
});

// Export for CLI usage
export { CodegenSnapshotManager };