/**
 * Git Hooks Setup for ae-framework Self-Improvement
 * 
 * This module sets up git hooks to enforce TDD compliance during development
 */

import * as fs from 'node:fs';
import * as path from 'node:path';

export interface GitHooksSetupConfig {
  projectRoot: string;
  forceOverwrite: boolean;
  enableTDDEnforcement: boolean;
}

export class GitHooksSetup {
  private config: GitHooksSetupConfig;

  constructor(config: Partial<GitHooksSetupConfig> = {}) {
    this.config = {
      projectRoot: process.cwd(),
      forceOverwrite: false,
      enableTDDEnforcement: true,
      ...config
    };
  }

  /**
   * Set up git hooks for TDD enforcement
   */
  async setupGitHooks(): Promise<{
    success: boolean;
    hooksInstalled: string[];
    message: string;
  }> {
    try {
      const gitDir = path.join(this.config.projectRoot, '.git');
      const hooksDir = path.join(gitDir, 'hooks');
      
      // Check if git repository exists
      if (!fs.existsSync(gitDir)) {
        return {
          success: false,
          hooksInstalled: [],
          message: 'Not a git repository - .git directory not found'
        };
      }

      // Ensure hooks directory exists
      if (!fs.existsSync(hooksDir)) {
        fs.mkdirSync(hooksDir, { recursive: true });
      }

      const hooksInstalled: string[] = [];

      // Install pre-commit hook
      const preCommitInstalled = await this.installPreCommitHook(hooksDir);
      if (preCommitInstalled) {
        hooksInstalled.push('pre-commit');
      }

      // Install pre-push hook (for additional validation)
      const prePushInstalled = await this.installPrePushHook(hooksDir);
      if (prePushInstalled) {
        hooksInstalled.push('pre-push');
      }

      const success = hooksInstalled.length > 0;

      return {
        success,
        hooksInstalled,
        message: success 
          ? `✅ Git hooks installed successfully: ${hooksInstalled.join(', ')}`
          : '❌ Failed to install git hooks'
      };

    } catch (error) {
      return {
        success: false,
        hooksInstalled: [],
        message: `Failed to setup git hooks: ${error instanceof Error ? error.message : error}`
      };
    }
  }

  /**
   * Install pre-commit hook
   */
  private async installPreCommitHook(hooksDir: string): Promise<boolean> {
    try {
      const hookPath = path.join(hooksDir, 'pre-commit');
      const sourcePath = path.join(this.config.projectRoot, 'scripts', 'hooks', 'pre-commit');

      // Check if source hook exists
      if (!fs.existsSync(sourcePath)) {
        console.warn('⚠️ Source pre-commit hook not found at:', sourcePath);
        return false;
      }

      // Check if hook already exists
      if (fs.existsSync(hookPath) && !this.config.forceOverwrite) {
        console.log('ℹ️ Pre-commit hook already exists, skipping installation');
        return true;
      }

      // Copy hook file
      fs.copyFileSync(sourcePath, hookPath);
      
      // Make executable
      fs.chmodSync(hookPath, 0o755);

      console.log('✅ Pre-commit hook installed and made executable');
      return true;

    } catch (error) {
      console.error('❌ Failed to install pre-commit hook:', error);
      return false;
    }
  }

  /**
   * Install pre-push hook for additional validation
   */
  private async installPrePushHook(hooksDir: string): Promise<boolean> {
    try {
      const hookPath = path.join(hooksDir, 'pre-push');

      // Check if hook already exists
      if (fs.existsSync(hookPath) && !this.config.forceOverwrite) {
        console.log('ℹ️ Pre-push hook already exists, skipping installation');
        return true;
      }

      // Create pre-push hook content
      const prePushContent = `#!/bin/sh
# ae-framework Self-Improvement pre-push hook
# Additional validation before pushing changes

set -e

echo "🚀 ae-framework Self-Improvement pre-push validation..."

# Run full test suite
echo "🧪 Running full test suite..."
if ! npm test; then
    echo "❌ Tests failing - push blocked"
    exit 1
fi

# Check TypeScript compilation
echo "🔧 Checking TypeScript compilation..."
if ! npx tsc --noEmit --strict; then
    echo "❌ TypeScript errors detected - push blocked"
    echo "   Goal: 287 → 0 errors for self-improvement"
    exit 1
fi

# Check for ae-framework-v2.yml configuration
if [ -f "ae-framework-v2.yml" ]; then
    echo "✅ Self-improvement configuration found"
else
    echo "⚠️ ae-framework-v2.yml not found - ensure self-improvement setup is complete"
fi

echo "✅ Pre-push validation passed - pushing changes..."
exit 0
`;

      // Write hook file
      fs.writeFileSync(hookPath, prePushContent);
      
      // Make executable
      fs.chmodSync(hookPath, 0o755);

      console.log('✅ Pre-push hook installed and made executable');
      return true;

    } catch (error) {
      console.error('❌ Failed to install pre-push hook:', error);
      return false;
    }
  }

  /**
   * Validate git hooks installation
   */
  async validateGitHooks(): Promise<{
    preCommitInstalled: boolean;
    prePushInstalled: boolean;
    allHooksWorking: boolean;
    issues: string[];
  }> {
    const gitDir = path.join(this.config.projectRoot, '.git');
    const hooksDir = path.join(gitDir, 'hooks');
    const issues: string[] = [];

    const preCommitPath = path.join(hooksDir, 'pre-commit');
    const prePushPath = path.join(hooksDir, 'pre-push');

    const preCommitInstalled = fs.existsSync(preCommitPath);
    const prePushInstalled = fs.existsSync(prePushPath);

    if (!preCommitInstalled) {
      issues.push('Pre-commit hook not installed');
    } else {
      // Check if executable
      try {
        const stats = fs.statSync(preCommitPath);
        if (!(stats.mode & 0o111)) {
          issues.push('Pre-commit hook not executable');
        }
      } catch (error) {
        issues.push('Cannot access pre-commit hook file');
      }
    }

    if (!prePushInstalled) {
      issues.push('Pre-push hook not installed');
    } else {
      // Check if executable
      try {
        const stats = fs.statSync(prePushPath);
        if (!(stats.mode & 0o111)) {
          issues.push('Pre-push hook not executable');
        }
      } catch (error) {
        issues.push('Cannot access pre-push hook file');
      }
    }

    const allHooksWorking = issues.length === 0;

    return {
      preCommitInstalled,
      prePushInstalled,
      allHooksWorking,
      issues
    };
  }

  /**
   * Uninstall git hooks (for cleanup)
   */
  async uninstallGitHooks(): Promise<{
    success: boolean;
    hooksRemoved: string[];
    message: string;
  }> {
    try {
      const gitDir = path.join(this.config.projectRoot, '.git');
      const hooksDir = path.join(gitDir, 'hooks');
      const hooksRemoved: string[] = [];

      const preCommitPath = path.join(hooksDir, 'pre-commit');
      const prePushPath = path.join(hooksDir, 'pre-push');

      // Remove pre-commit hook
      if (fs.existsSync(preCommitPath)) {
        fs.unlinkSync(preCommitPath);
        hooksRemoved.push('pre-commit');
      }

      // Remove pre-push hook
      if (fs.existsSync(prePushPath)) {
        fs.unlinkSync(prePushPath);
        hooksRemoved.push('pre-push');
      }

      return {
        success: true,
        hooksRemoved,
        message: hooksRemoved.length > 0 
          ? `✅ Git hooks removed: ${hooksRemoved.join(', ')}`
          : 'ℹ️ No git hooks found to remove'
      };

    } catch (error) {
      return {
        success: false,
        hooksRemoved: [],
        message: `Failed to uninstall git hooks: ${error instanceof Error ? error.message : error}`
      };
    }
  }
}

// Export factory function
export const createGitHooksSetup = (config?: Partial<GitHooksSetupConfig>) => {
  return new GitHooksSetup(config);
};