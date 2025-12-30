#!/usr/bin/env node

/**
 * Release Operations Manager
 * Comprehensive release automation for ae-framework
 */

import { execSync } from 'child_process';
import { existsSync, readFileSync, writeFileSync, mkdirSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

class ReleaseOperationsManager {
  constructor() {
    this.projectRoot = join(__dirname, '..');
    this.releaseDir = join(this.projectRoot, 'releases');
    this.timestamp = new Date().toISOString().replace(/[:.]/g, '-');
  }

  async analyze() {
    console.log('🚀 Analyzing release operations setup...\n');
    
    this.ensureReleaseDirectory();
    
    const results = {
      timestamp: new Date().toISOString(),
      summary: {
        totalChecks: 6,
        passed: 0,
        failed: 0,
        warnings: 0
      },
      checks: {
        changesetSetup: await this.checkChangesetSetup(),
        versioningStrategy: await this.checkVersioningStrategy(),
        changelogGeneration: await this.checkChangelogGeneration(),
        releaseWorkflow: await this.checkReleaseWorkflow(),
        npmPublishing: await this.checkNpmPublishing(),
        releaseValidation: await this.checkReleaseValidation()
      }
    };

    // Calculate summary
    Object.values(results.checks).forEach(check => {
      if (check.status === 'passed') results.summary.passed++;
      else if (check.status === 'failed') results.summary.failed++;
      else if (check.status === 'warning') results.summary.warnings++;
    });

    // Generate report
    await this.generateReport(results);
    
    console.log('\n📊 Release Operations Analysis Summary:');
    console.log(`✅ Passed: ${results.summary.passed}`);
    console.log(`❌ Failed: ${results.summary.failed}`);
    console.log(`⚠️  Warnings: ${results.summary.warnings}`);
    
    const overallScore = (results.summary.passed / results.summary.totalChecks) * 100;
    console.log(`🚀 Release Operations Score: ${overallScore.toFixed(1)}%`);
    
    return results;
  }

  async setupReleaseOperations() {
    console.log('🔧 Setting up complete release operations...\n');
    
    await this.setupChangesets();
    await this.setupReleaseWorkflow();
    await this.setupChangelogAutomation();
    await this.setupVersionBumping();
    
    console.log('✅ Release operations setup completed!');
  }

  async checkChangesetSetup() {
    console.log('📦 Checking Changesets configuration...');
    
    try {
      const changesetConfig = join(this.projectRoot, '.changeset/config.json');
      const changesetDir = join(this.projectRoot, '.changeset');
      
      if (!existsSync(changesetDir)) {
        console.log('  ⚠️  Changesets not initialized');
        return {
          status: 'failed',
          tool: 'Changesets',
          details: ['Changesets not initialized - run setup to configure']
        };
      }
      
      if (existsSync(changesetConfig)) {
        const config = JSON.parse(readFileSync(changesetConfig, 'utf-8'));
        console.log('  ✅ Changesets properly configured');
        
        return {
          status: 'passed',
          tool: 'Changesets',
          details: [
            'Changesets configuration found',
            `Changelog: ${config.changelog ? 'enabled' : 'disabled'}`,
            `Commit: ${config.commit ? 'enabled' : 'disabled'}`
          ]
        };
      } else {
        return {
          status: 'warning',
          tool: 'Changesets',
          details: ['Changesets directory exists but missing config.json']
        };
      }
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Changesets',
        details: [`Changesets check failed: ${error.message}`]
      };
    }
  }

  async checkVersioningStrategy() {
    console.log('🔢 Checking versioning strategy...');
    
    try {
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      const currentVersion = packageJson.version;
      
      // Check for semantic versioning
      const semverRegex = /^\\d+\\.\\d+\\.\\d+/;
      const isValidSemver = semverRegex.test(currentVersion);
      
      // Check for release scripts
      const releaseScripts = [
        'version:patch',
        'version:minor',
        'version:major',
        'release:patch',
        'release:minor',
        'release:major'
      ];
      
      const hasReleaseScripts = releaseScripts.some(script => 
        packageJson.scripts && packageJson.scripts[script]
      );
      
      console.log(`  📊 Current version: ${currentVersion}`);
      
      return {
        status: isValidSemver ? 'passed' : 'failed',
        tool: 'Semantic Versioning',
        details: [
          `Current version: ${currentVersion}`,
          `Valid semver: ${isValidSemver ? 'Yes' : 'No'}`,
          `Release scripts: ${hasReleaseScripts ? 'Configured' : 'Missing'}`
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Semantic Versioning',
        details: [`Version check failed: ${error.message}`]
      };
    }
  }

  async checkChangelogGeneration() {
    console.log('📝 Checking changelog generation...');
    
    try {
      const changelogPath = join(this.projectRoot, 'CHANGELOG.md');
      const hasChangelog = existsSync(changelogPath);
      
      // Check for changelog generation tools
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      const changelogTools = [
        '@changesets/cli',
        'conventional-changelog',
        'auto-changelog',
        'standard-version'
      ];
      
      const installedTools = changelogTools.filter(tool => 
        packageJson.dependencies?.[tool] || packageJson.devDependencies?.[tool]
      );
      
      console.log(`  📋 Changelog exists: ${hasChangelog}`);
      
      return {
        status: hasChangelog && installedTools.length > 0 ? 'passed' : 'warning',
        tool: 'Changelog Generation',
        details: [
          `CHANGELOG.md exists: ${hasChangelog}`,
          `Changelog tools: ${installedTools.length > 0 ? installedTools.join(', ') : 'None'}`,
          hasChangelog ? 'Automated changelog generation ready' : 'Manual changelog management'
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Changelog Generation',
        details: [`Changelog check failed: ${error.message}`]
      };
    }
  }

  async checkReleaseWorkflow() {
    console.log('⚙️  Checking release workflow automation...');
    
    try {
      const workflowDir = join(this.projectRoot, '.github/workflows');
      const releaseWorkflowFiles = [
        'release.yml',
        'release.yaml',
        'publish.yml',
        'publish.yaml'
      ];
      
      let foundWorkflow = false;
      let workflowDetails = [];
      
      if (existsSync(workflowDir)) {
        for (const file of releaseWorkflowFiles) {
          const workflowPath = join(workflowDir, file);
          if (existsSync(workflowPath)) {
            foundWorkflow = true;
            const content = readFileSync(workflowPath, 'utf-8');
            
            // Check for key workflow features
            const hasVersionBump = content.includes('changeset') || content.includes('version');
            const hasPublish = content.includes('npm publish') || content.includes('yarn publish');
            const hasTagging = content.includes('git tag') || content.includes('create-tag');
            
            workflowDetails.push(`Found ${file}`);
            if (hasVersionBump) workflowDetails.push('✅ Version bumping');
            if (hasPublish) workflowDetails.push('✅ NPM publishing');
            if (hasTagging) workflowDetails.push('✅ Git tagging');
            
            break;
          }
        }
      }
      
      console.log(`  🔄 Release workflow: ${foundWorkflow ? 'Found' : 'Missing'}`);
      
      return {
        status: foundWorkflow ? 'passed' : 'failed',
        tool: 'GitHub Actions',
        details: foundWorkflow 
          ? workflowDetails
          : ['No release workflow found - setup required']
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'GitHub Actions',
        details: [`Workflow check failed: ${error.message}`]
      };
    }
  }

  async checkNpmPublishing() {
    console.log('📦 Checking NPM publishing configuration...');
    
    try {
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      
      // Check publishing configuration
      const publishConfig = packageJson.publishConfig || {};
      const isPrivate = packageJson.private === true;
      const hasRegistry = publishConfig.registry || process.env.NPM_REGISTRY;
      
      // Check for npmrc
      const npmrcPath = join(this.projectRoot, '.npmrc');
      const hasNpmrc = existsSync(npmrcPath);
      
      // Check for publishing scripts
      const publishScripts = [
        'prepublishOnly',
        'postpublish',
        'publish:npm',
        'release:publish'
      ];
      
      const hasPublishScripts = publishScripts.some(script => 
        packageJson.scripts && packageJson.scripts[script]
      );
      
      console.log(`  📋 Package private: ${isPrivate}`);
      
      return {
        status: !isPrivate ? 'passed' : 'warning',
        tool: 'NPM Publishing',
        details: [
          `Package private: ${isPrivate}`,
          `Registry configured: ${hasRegistry ? 'Yes' : 'No'}`,
          `.npmrc exists: ${hasNpmrc}`,
          `Publish scripts: ${hasPublishScripts ? 'Configured' : 'Missing'}`
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'NPM Publishing',
        details: [`NPM config check failed: ${error.message}`]
      };
    }
  }

  async checkReleaseValidation() {
    console.log('✅ Checking release validation...');
    
    try {
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      
      // Check for pre-release validation scripts
      const validationScripts = [
        'prerelease',
        'test:ci',
        'build:prod',
        'lint:ci',
        'security:audit'
      ];
      
      const hasValidation = validationScripts.some(script => 
        packageJson.scripts && packageJson.scripts[script]
      );
      
      // Check for quality gates
      const qualityGates = [
        'test',
        'lint',
        'type-check',
        'build'
      ];
      
      const hasQualityGates = qualityGates.every(gate => 
        packageJson.scripts && packageJson.scripts[gate]
      );
      
      console.log(`  🔍 Quality gates: ${hasQualityGates ? 'Complete' : 'Partial'}`);
      
      return {
        status: hasValidation && hasQualityGates ? 'passed' : 'warning',
        tool: 'Release Validation',
        details: [
          `Pre-release validation: ${hasValidation ? 'Configured' : 'Missing'}`,
          `Quality gates: ${hasQualityGates ? 'Complete' : 'Partial'}`,
          'All checks should pass before release'
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Release Validation',
        details: [`Validation check failed: ${error.message}`]
      };
    }
  }

  // Setup methods
  async setupChangesets() {
    console.log('🔧 Setting up Changesets...');
    
    try {
      // Initialize changesets if not exists
      if (!existsSync(join(this.projectRoot, '.changeset'))) {
        execSync('npx @changesets/cli init', {
          cwd: this.projectRoot,
          stdio: 'inherit'
        });
      }
      
      // Configure changesets
      const changesetConfig = {
        $schema: "https://unpkg.com/@changesets/config@2.3.1/schema.json",
        changelog: "@changesets/cli/changelog",
        commit: false,
        fixed: [],
        linked: [],
        access: "public",
        baseBranch: "main",
        updateInternalDependencies: "patch",
        ignore: []
      };
      
      writeFileSync(
        join(this.projectRoot, '.changeset/config.json'),
        JSON.stringify(changesetConfig, null, 2)
      );
      
      console.log('  ✅ Changesets configured');
      
    } catch (error) {
      console.error(`  ❌ Changesets setup failed: ${error.message}`);
    }
  }

  async setupReleaseWorkflow() {
    console.log('🔧 Setting up release workflow...');
    
    const workflowDir = join(this.projectRoot, '.github/workflows');
    mkdirSync(workflowDir, { recursive: true });
    
    const ghaConcurrency = '${{ github.workflow }}-${{ github.ref }}';
    const releaseWorkflow = `name: Release

on:
  push:
    branches:
      - main
  workflow_dispatch:

concurrency: ${ghaConcurrency}

jobs:
  release:
    name: Release
    runs-on: ubuntu-latest
    
    permissions:
      contents: write
      pull-requests: write
      
    steps:
      - name: Checkout
        uses: actions/checkout@v4
        with:
          # This makes Actions fetch all Git history so that Changesets can generate CHANGELOGs with the correct commits
          fetch-depth: 0
          
      - name: Setup Node.js
        uses: actions/setup-node@v4
        with:
          node-version: '18'
          cache: 'npm'
          
      - name: Install dependencies
        run: npm ci
        
      - name: Run quality checks
        run: |
          npm run lint
          npm run type-check || npm run test:types || true
          npm run test
          npm run build
          
      - name: Run security audit
        run: npm audit --audit-level=moderate
        
      - name: Create Release Pull Request or Publish to npm
        id: changesets
        uses: changesets/action@v1
        with:
          # This expects you to have a script called release which does a build for your packages and calls changeset publish
          publish: npm run release
          commit: "chore: release packages"
          title: "chore: release packages"
        env:
          GITHUB_TOKEN: \\${{ secrets.GITHUB_TOKEN }}
          NPM_TOKEN: \\${{ secrets.NPM_TOKEN }}
          
      - name: Create GitHub Release
        if: steps.changesets.outputs.published == 'true'
        uses: actions/create-release@v1
        env:
          GITHUB_TOKEN: \\${{ secrets.GITHUB_TOKEN }}
        with:
          tag_name: v\\${{ steps.changesets.outputs.version }}
          release_name: Release v\\${{ steps.changesets.outputs.version }}
          body: \\${{ steps.changesets.outputs.changelog }}
          draft: false
          prerelease: false
`;

    writeFileSync(join(workflowDir, 'release.yml'), releaseWorkflow);
    console.log('  ✅ Release workflow created');
  }

  async setupChangelogAutomation() {
    console.log('🔧 Setting up changelog automation...');
    
    // Add release scripts to package.json
    const packageJsonPath = join(this.projectRoot, 'package.json');
    const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));
    
    packageJson.scripts = {
      ...packageJson.scripts,
      'changeset': 'changeset',
      'changeset:version': 'changeset version',
      'changeset:publish': 'changeset publish',
      'changeset:status': 'changeset status',
      'release': 'npm run build && changeset publish',
      'release:snapshot': 'changeset version --snapshot',
      'version:patch': 'changeset version && git add . && git commit -m "chore: version bump"',
      'version:check': 'changeset status --verbose'
    };
    
    writeFileSync(packageJsonPath, JSON.stringify(packageJson, null, 2));
    console.log('  ✅ Release scripts added to package.json');
  }

  async setupVersionBumping() {
    console.log('🔧 Setting up automated version bumping...');
    
    // Create pre-commit hook for version validation
    const hooksDir = join(this.projectRoot, 'scripts/hooks');
    mkdirSync(hooksDir, { recursive: true });
    
    const versionHook = `#!/bin/bash
# Pre-release version validation

echo "🔍 Validating version changes..."

# Check if this is a release commit
if git diff --cached --name-only | grep -q "package.json"; then
    echo "📦 Package.json changes detected"
    
    # Run quality checks
    npm run lint || exit 1
    npm run test || exit 1
    npm run build || exit 1
    
    echo "✅ Version validation passed"
fi
`;

    writeFileSync(join(hooksDir, 'pre-release'), versionHook);
    console.log('  ✅ Version validation hook created');
  }

  ensureReleaseDirectory() {
    if (!existsSync(this.releaseDir)) {
      mkdirSync(this.releaseDir, { recursive: true });
    }
  }

  async generateReport(results) {
    const reportPath = join(this.releaseDir, `release-ops-report-${this.timestamp}.json`);
    writeFileSync(reportPath, JSON.stringify(results, null, 2));
    
    // Generate human-readable report
    const htmlReport = this.generateHTMLReport(results);
    const htmlPath = join(this.releaseDir, `release-ops-report-${this.timestamp}.html`);
    writeFileSync(htmlPath, htmlReport);
    
    console.log(`\n📋 Release operations report generated:`);
    console.log(`   JSON: ${reportPath}`);
    console.log(`   HTML: ${htmlPath}`);
  }

  generateHTMLReport(results) {
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Release Operations Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 40px; line-height: 1.6; }
        .header { background: #f8f9fa; padding: 20px; border-radius: 8px; }
        .summary { display: flex; gap: 20px; margin: 20px 0; flex-wrap: wrap; }
        .metric { padding: 15px; border-radius: 8px; text-align: center; min-width: 120px; }
        .passed { background: #d4edda; color: #155724; }
        .failed { background: #f8d7da; color: #721c24; }
        .warning { background: #fff3cd; color: #856404; }
        .check { margin: 20px 0; padding: 15px; border-left: 4px solid #ccc; }
        .check.passed { border-color: #28a745; }
        .check.failed { border-color: #dc3545; }
        .check.warning { border-color: #ffc107; }
        .details { margin: 10px 0; }
        .details li { margin: 5px 0; }
        .icon { font-size: 1.2em; margin-right: 8px; }
    </style>
</head>
<body>
    <div class="header">
        <h1><span class="icon">🚀</span>Release Operations Report</h1>
        <p><strong>Generated:</strong> ${results.timestamp}</p>
        <p><strong>Overall Score:</strong> ${((results.summary.passed / results.summary.totalChecks) * 100).toFixed(1)}%</p>
    </div>
    
    <div class="summary">
        <div class="metric passed">
            <h3>${results.summary.passed}</h3>
            <p>Passed</p>
        </div>
        <div class="metric failed">
            <h3>${results.summary.failed}</h3>
            <p>Failed</p>
        </div>
        <div class="metric warning">
            <h3>${results.summary.warnings}</h3>
            <p>Warnings</p>
        </div>
    </div>
    
    <h2>Release Operations Checks</h2>
    ${Object.entries(results.checks).map(([name, check]) => `
        <div class="check ${check.status}">
            <h3>${name.replace(/([A-Z])/g, ' $1').replace(/^./, str => str.toUpperCase())} (${check.tool})</h3>
            <p><strong>Status:</strong> ${check.status.toUpperCase()}</p>
            <div class="details">
                <ul>
                    ${check.details.map(detail => `<li>${detail}</li>`).join('')}
                </ul>
            </div>
        </div>
    `).join('')}
    
    <h2>Release Operations Best Practices</h2>
    <ul>
        <li>Use semantic versioning for all releases</li>
        <li>Automate changelog generation from commits</li>
        <li>Implement comprehensive pre-release validation</li>
        <li>Use Changesets for monorepo version management</li>
        <li>Automate NPM publishing through CI/CD</li>
        <li>Create Git tags for all releases</li>
        <li>Generate release notes automatically</li>
        <li>Implement rollback procedures</li>
    </ul>
    
    <h2>Quick Setup Commands</h2>
    <pre><code># Initialize Changesets
npx @changesets/cli init

# Add a changeset
npx changeset

# Version packages
npx changeset version

# Publish packages
npx changeset publish

# Check changeset status
npx changeset status</code></pre>
</body>
</html>`;
  }
}

// CLI execution
if (import.meta.url === `file://${process.argv[1]}`) {
  const manager = new ReleaseOperationsManager();
  
  const command = process.argv[2];
  
  if (command === 'setup') {
    manager.setupReleaseOperations().catch(error => {
      console.error('Release operations setup failed:', error);
      process.exit(1);
    });
  } else {
    manager.analyze().catch(error => {
      console.error('Release operations analysis failed:', error);
      process.exit(1);
    });
  }
}

export { ReleaseOperationsManager };
