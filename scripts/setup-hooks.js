#!/usr/bin/env node

/**
 * Cross-platform Git hooks setup script
 * Replaces Unix-specific commands with Node.js cross-platform alternatives
 */

const fs = require('fs');
const path = require('path');
const os = require('os');

class GitHooksSetup {
  constructor() {
    this.isWindows = os.platform() === 'win32';
    this.gitHooksDir = path.join(process.cwd(), '.git', 'hooks');
    this.scriptsDir = path.join(process.cwd(), 'scripts', 'hooks');
  }

  async ensureGitHooksDirectory() {
    console.log('📁 Ensuring .git/hooks directory exists...');
    
    try {
      await fs.promises.access(this.gitHooksDir);
    } catch (error) {
      if (error.code === 'ENOENT') {
        await fs.promises.mkdir(this.gitHooksDir, { recursive: true });
        console.log('✅ Created .git/hooks directory');
      } else {
        throw error;
      }
    }
  }

  async copyHookFile(hookName) {
    const sourcePath = path.join(this.scriptsDir, hookName);
    const destPath = path.join(this.gitHooksDir, hookName);
    
    console.log(`📋 Copying ${hookName} hook...`);
    
    try {
      // Check if source file exists
      await fs.promises.access(sourcePath);
      
      // Copy the hook file
      await fs.promises.copyFile(sourcePath, destPath);
      
      // Make executable (Unix/Mac only)
      if (!this.isWindows) {
        await fs.promises.chmod(destPath, 0o755);
        console.log(`✅ Copied and made executable: ${hookName}`);
      } else {
        console.log(`✅ Copied: ${hookName} (Windows - executable flag not needed)`);
      }
      
    } catch (error) {
      if (error.code === 'ENOENT') {
        console.warn(`⚠️ Hook file not found: ${sourcePath}`);
      } else {
        throw error;
      }
    }
  }

  async setupAllHooks() {
    console.log('🚀 Setting up Git hooks...');
    console.log(`📍 Platform: ${this.isWindows ? 'Windows' : 'Unix/Mac'}`);
    
    await this.ensureGitHooksDirectory();
    
    // Common Git hook files to setup
    const hookFiles = [
      'pre-commit',
      'pre-commit-spec-validation',
      'pre-push',
      'commit-msg'
    ];
    
    for (const hookFile of hookFiles) {
      await this.copyHookFile(hookFile);
    }
  }

  async verifySetup() {
    console.log('🔍 Verifying hook setup...');
    
    const hookFiles = await fs.promises.readdir(this.gitHooksDir);
    const installedHooks = hookFiles.filter(file => !file.endsWith('.sample'));
    
    if (installedHooks.length > 0) {
      console.log('✅ Installed hooks:');
      installedHooks.forEach(hook => {
        console.log(`   • ${hook}`);
      });
    } else {
      console.log('⚠️ No hooks were installed');
    }
  }

  async displayUsageInfo() {
    console.log('\n📖 Git Hooks Usage Information:');
    console.log('');
    console.log('🔧 Pre-commit Hook:');
    console.log('   • Runs TypeScript type checking');
    console.log('   • Validates code formatting');
    console.log('   • Checks for common issues');
    console.log('');
    console.log('📝 Pre-commit Spec Validation:');
    console.log('   • Validates specification files');
    console.log('   • Ensures proper format and structure');
    console.log('');
    console.log('🚫 To skip hooks temporarily:');
    console.log('   git commit --no-verify -m "message"');
    console.log('');
    console.log('🔄 To reinstall hooks:');
    if (this.isWindows) {
      console.log('   node scripts/setup-hooks.js');
    } else {
      console.log('   npm run setup-hooks');
    }
  }
}

async function main() {
  const setup = new GitHooksSetup();
  
  try {
    await setup.setupAllHooks();
    await setup.verifySetup();
    await setup.displayUsageInfo();
    
    console.log('\n✅ Git hooks setup completed successfully!');
    
  } catch (error) {
    console.error('\n❌ Error setting up Git hooks:');
    console.error(error.message);
    
    if (error.code === 'ENOENT' && error.path?.includes('.git')) {
      console.error('\n💡 Make sure you are in a Git repository root directory.');
      console.error('   Run "git init" if this is a new repository.');
    }
    
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

module.exports = { GitHooksSetup };