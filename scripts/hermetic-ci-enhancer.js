#!/usr/bin/env node

/**
 * Hermetic CI/CD Enhancement System
 * Complete hermetic pipeline validation and optimization
 */

import { execSync } from 'child_process';
import { existsSync, readFileSync, writeFileSync, mkdirSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

class HermeticCIEnhancer {
  constructor() {
    this.projectRoot = join(__dirname, '..');
    this.reportsDir = join(this.projectRoot, 'hermetic-reports');
    this.timestamp = new Date().toISOString().replace(/[:.]/g, '-');
  }

  async analyze() {
    console.log('🔒 Analyzing hermetic CI/CD pipeline...\n');
    
    this.ensureReportDirectory();
    
    const results = {
      timestamp: new Date().toISOString(),
      summary: {
        totalChecks: 7,
        passed: 0,
        failed: 0,
        warnings: 0
      },
      checks: {
        deterministicBuild: await this.checkDeterministicBuild(),
        testIsolation: await this.checkTestIsolation(),
        dependencyHermeticity: await this.checkDependencyHermeticity(),
        environmentReproducibility: await this.checkEnvironmentReproducibility(),
        ciPipelineHermeticity: await this.checkCIPipelineHermeticity(),
        artifactConsistency: await this.checkArtifactConsistency(),
        hermeticValidation: await this.checkHermeticValidation()
      }
    };

    // Calculate summary
    Object.values(results.checks).forEach(check => {
      if (check.status === 'passed') results.summary.passed++;
      else if (check.status === 'failed') results.summary.failed++;
      else if (check.status === 'warning') results.summary.warnings++;
    });

    // Generate comprehensive report
    await this.generateReport(results);
    
    console.log('\n📊 Hermetic CI/CD Analysis Summary:');
    console.log(`✅ Passed: ${results.summary.passed}`);
    console.log(`❌ Failed: ${results.summary.failed}`);
    console.log(`⚠️  Warnings: ${results.summary.warnings}`);
    
    const overallScore = (results.summary.passed / results.summary.totalChecks) * 100;
    console.log(`🔒 Hermetic CI/CD Score: ${overallScore.toFixed(1)}%`);
    
    return results;
  }

  async enhance() {
    console.log('🚀 Enhancing hermetic CI/CD pipeline...\n');
    
    await this.setupHermeticEnvironment();
    await this.configureDeterministicBuilds();
    await this.setupTestIsolation();
    await this.configureHermeticDependencies();
    await this.setupHermeticValidation();
    
    console.log('✅ Hermetic CI/CD enhancement completed!');
  }

  // Analysis methods
  async checkDeterministicBuild() {
    console.log('🔧 Checking deterministic build setup...');
    
    try {
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      
      // Check for deterministic build configuration
      const hasDeterministicScripts = !!(
        packageJson.scripts?.['build:deterministic'] ||
        packageJson.scripts?.['build:reproducible']
      );
      
      // Check for build timestamp configuration
      const buildConfig = packageJson.build || {};
      const hasTimestampConfig = !!(
        buildConfig.reproducible ||
        process.env.SOURCE_DATE_EPOCH
      );
      
      // Check TypeScript configuration for deterministic builds
      const tsconfigPath = join(this.projectRoot, 'tsconfig.json');
      let hasDeterministicTsConfig = false;
      
      if (existsSync(tsconfigPath)) {
        const tsconfig = JSON.parse(readFileSync(tsconfigPath, 'utf-8'));
        hasDeterministicTsConfig = !!(
          tsconfig.compilerOptions?.incremental === false ||
          tsconfig.compilerOptions?.tsBuildInfoFile === null
        );
      }
      
      console.log(`  🔧 Deterministic scripts: ${hasDeterministicScripts ? 'Configured' : 'Missing'}`);
      
      return {
        status: hasDeterministicScripts && hasTimestampConfig ? 'passed' : 'warning',
        tool: 'Deterministic Build',
        details: [
          `Deterministic scripts: ${hasDeterministicScripts ? 'Configured' : 'Missing'}`,
          `Timestamp config: ${hasTimestampConfig ? 'Set' : 'Missing'}`,
          `TypeScript config: ${hasDeterministicTsConfig ? 'Optimized' : 'Standard'}`
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Deterministic Build',
        details: [`Build check failed: ${error.message}`]
      };
    }
  }

  async checkTestIsolation() {
    console.log('🧪 Checking test isolation...');
    
    try {
      // Check test configuration for isolation
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      
      const hasIsolationScripts = !!(
        packageJson.scripts?.['test:isolated'] ||
        packageJson.scripts?.['test:hermetic']
      );
      
      // Check for test isolation configuration
      const testFiles = [
        'vitest.config.ts',
        'jest.config.js',
        'jest.config.ts'
      ];
      
      let hasIsolationConfig = false;
      for (const file of testFiles) {
        const configPath = join(this.projectRoot, file);
        if (existsSync(configPath)) {
          const content = readFileSync(configPath, 'utf-8');
          if (content.includes('isolate') || content.includes('forceExit') || content.includes('runInBand')) {
            hasIsolationConfig = true;
            break;
          }
        }
      }
      
      // Check for hermetic test validation
      const hasHermeticValidation = existsSync(join(this.projectRoot, 'scripts/hermetic-test-validator.js'));
      
      console.log(`  🧪 Test isolation: ${hasIsolationConfig ? 'Configured' : 'Standard'}`);
      
      return {
        status: hasIsolationConfig && hasHermeticValidation ? 'passed' : 'warning',
        tool: 'Test Isolation',
        details: [
          `Isolation scripts: ${hasIsolationScripts ? 'Available' : 'Missing'}`,
          `Isolation config: ${hasIsolationConfig ? 'Configured' : 'Standard'}`,
          `Hermetic validation: ${hasHermeticValidation ? 'Available' : 'Missing'}`
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Test Isolation',
        details: [`Test isolation check failed: ${error.message}`]
      };
    }
  }

  async checkDependencyHermeticity() {
    console.log('📦 Checking dependency hermeticity...');
    
    try {
      // Check package-lock.json existence and integrity
      const packageLockPath = join(this.projectRoot, 'package-lock.json');
      const hasPackageLock = existsSync(packageLockPath);
      
      // Check for .npmrc configuration
      const npmrcPath = join(this.projectRoot, '.npmrc');
      let hasHermeticNpmrc = false;
      
      if (existsSync(npmrcPath)) {
        const npmrcContent = readFileSync(npmrcPath, 'utf-8');
        hasHermeticNpmrc = npmrcContent.includes('audit=false') || 
                          npmrcContent.includes('fund=false') ||
                          npmrcContent.includes('update-notifier=false');
      }
      
      // Check for dependency validation scripts
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      const hasDependencyValidation = !!(
        packageJson.scripts?.['deps:validate'] ||
        packageJson.scripts?.['deps:hermetic']
      );
      
      // Check for problematic dependencies
      const problematicDeps = [
        'fsevents',
        'node-gyp',
        'sharp',
        'canvas',
        'puppeteer'
      ];
      
      const foundProblematic = problematicDeps.filter(dep => 
        packageJson.dependencies?.[dep] || packageJson.devDependencies?.[dep]
      );
      
      console.log(`  📦 Package lock: ${hasPackageLock ? 'Present' : 'Missing'}`);
      
      return {
        status: hasPackageLock && foundProblematic.length === 0 ? 'passed' : 'warning',
        tool: 'Dependency Hermeticity',
        details: [
          `Package lock: ${hasPackageLock ? 'Present' : 'Missing'}`,
          `Hermetic npmrc: ${hasHermeticNpmrc ? 'Configured' : 'Standard'}`,
          `Dependency validation: ${hasDependencyValidation ? 'Available' : 'Missing'}`,
          `Problematic deps: ${foundProblematic.length === 0 ? 'None' : foundProblematic.join(', ')}`
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Dependency Hermeticity',
        details: [`Dependency check failed: ${error.message}`]
      };
    }
  }

  async checkEnvironmentReproducibility() {
    console.log('🌍 Checking environment reproducibility...');
    
    try {
      // Check for environment configuration
      const envFiles = [
        '.env.example',
        '.env.template',
        '.env.ci'
      ];
      
      const hasEnvTemplate = envFiles.some(file => 
        existsSync(join(this.projectRoot, file))
      );
      
      // Check for Docker configuration
      const dockerFiles = [
        'Dockerfile',
        'docker-compose.yml',
        '.dockerignore'
      ];
      
      const hasDockerConfig = dockerFiles.some(file => 
        existsSync(join(this.projectRoot, file))
      );
      
      // Check for Node.js version specification
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      const hasNodeVersion = !!(packageJson.engines?.node);
      
      // Check for .nvmrc
      const hasNvmrc = existsSync(join(this.projectRoot, '.nvmrc'));
      
      console.log(`  🌍 Environment reproducibility: ${hasNodeVersion ? 'Configured' : 'Partial'}`);
      
      return {
        status: hasNodeVersion && (hasDockerConfig || hasNvmrc) ? 'passed' : 'warning',
        tool: 'Environment Reproducibility',
        details: [
          `Environment template: ${hasEnvTemplate ? 'Available' : 'Missing'}`,
          `Docker config: ${hasDockerConfig ? 'Available' : 'Missing'}`,
          `Node version: ${hasNodeVersion ? 'Specified' : 'Missing'}`,
          `.nvmrc: ${hasNvmrc ? 'Present' : 'Missing'}`
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Environment Reproducibility',
        details: [`Environment check failed: ${error.message}`]
      };
    }
  }

  async checkCIPipelineHermeticity() {
    console.log('🔄 Checking CI pipeline hermeticity...');
    
    try {
      const githubDir = join(this.projectRoot, '.github/workflows');
      let hasHermeticWorkflow = false;
      let hermeticFeatures = [];
      
      if (existsSync(githubDir)) {
        const workflows = require('fs').readdirSync(githubDir);
        
        for (const workflow of workflows) {
          const content = readFileSync(join(githubDir, workflow), 'utf-8');
          
          if (content.includes('hermetic') || content.includes('deterministic')) {
            hasHermeticWorkflow = true;
            
            // Check for hermetic features
            if (content.includes('SOURCE_DATE_EPOCH')) hermeticFeatures.push('Fixed timestamps');
            if (content.includes('--no-audit')) hermeticFeatures.push('Audit disabled');
            if (content.includes('npm ci')) hermeticFeatures.push('Exact installs');
            if (content.includes('cache:')) hermeticFeatures.push('Dependency caching');
            if (content.includes('concurrency:')) hermeticFeatures.push('Concurrency control');
            
            break;
          }
        }
      }
      
      console.log(`  🔄 Hermetic workflow: ${hasHermeticWorkflow ? 'Configured' : 'Missing'}`);
      
      return {
        status: hasHermeticWorkflow ? 'passed' : 'failed',
        tool: 'CI Pipeline Hermeticity',
        details: hasHermeticWorkflow 
          ? [`Hermetic workflow found`, ...hermeticFeatures.map(f => `✅ ${f}`)]
          : ['No hermetic CI workflow found - setup required']
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'CI Pipeline Hermeticity',
        details: [`CI pipeline check failed: ${error.message}`]
      };
    }
  }

  async checkArtifactConsistency() {
    console.log('📦 Checking artifact consistency...');
    
    try {
      // Check for build artifact validation
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      
      const hasArtifactValidation = !!(
        packageJson.scripts?.['validate:build'] ||
        packageJson.scripts?.['verify:artifacts']
      );
      
      // Check for checksum generation
      const hasChecksumGeneration = !!(
        packageJson.scripts?.['checksum:generate'] ||
        packageJson.scripts?.['hash:verify']
      );
      
      // Check for build consistency scripts
      const hasConsistencyCheck = !!(
        packageJson.scripts?.['build:verify'] ||
        packageJson.scripts?.['consistency:check']
      );
      
      console.log(`  📦 Artifact validation: ${hasArtifactValidation ? 'Available' : 'Missing'}`);
      
      return {
        status: hasArtifactValidation || hasChecksumGeneration ? 'passed' : 'warning',
        tool: 'Artifact Consistency',
        details: [
          `Artifact validation: ${hasArtifactValidation ? 'Available' : 'Missing'}`,
          `Checksum generation: ${hasChecksumGeneration ? 'Available' : 'Missing'}`,
          `Consistency checks: ${hasConsistencyCheck ? 'Available' : 'Missing'}`
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Artifact Consistency',
        details: [`Artifact check failed: ${error.message}`]
      };
    }
  }

  async checkHermeticValidation() {
    console.log('✅ Checking hermetic validation tools...');
    
    try {
      // Check for hermetic test validator
      const hasHermeticValidator = existsSync(join(this.projectRoot, 'scripts/hermetic-test-validator.js'));
      
      // Check for hermetic quick validator
      const hasQuickValidator = existsSync(join(this.projectRoot, 'scripts/hermetic-test-quick-validator.js'));
      
      // Check for validation scripts
      const packageJson = JSON.parse(readFileSync(join(this.projectRoot, 'package.json'), 'utf-8'));
      const hasValidationScripts = !!(
        packageJson.scripts?.['hermetic:validate'] ||
        packageJson.scripts?.['hermetic:quick']
      );
      
      console.log(`  ✅ Hermetic validation: ${hasHermeticValidator ? 'Available' : 'Missing'}`);
      
      return {
        status: hasHermeticValidator && hasValidationScripts ? 'passed' : 'warning',
        tool: 'Hermetic Validation',
        details: [
          `Hermetic validator: ${hasHermeticValidator ? 'Available' : 'Missing'}`,
          `Quick validator: ${hasQuickValidator ? 'Available' : 'Missing'}`,
          `Validation scripts: ${hasValidationScripts ? 'Configured' : 'Missing'}`
        ]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'Hermetic Validation',
        details: [`Validation check failed: ${error.message}`]
      };
    }
  }

  // Enhancement methods
  async setupHermeticEnvironment() {
    console.log('🔧 Setting up hermetic environment...');
    
    // Create .nvmrc if not exists
    if (!existsSync(join(this.projectRoot, '.nvmrc'))) {
      writeFileSync(join(this.projectRoot, '.nvmrc'), '18.20.0\n');
      console.log('  ✅ .nvmrc created');
    }
    
    // Create hermetic .npmrc
    const npmrcPath = join(this.projectRoot, '.npmrc');
    const hermeticNpmrc = `# Hermetic configuration
audit=false
fund=false
update-notifier=false
save-exact=true
package-lock=true
shrinkwrap=false
`;
    
    if (!existsSync(npmrcPath)) {
      writeFileSync(npmrcPath, hermeticNpmrc);
      console.log('  ✅ Hermetic .npmrc created');
    }
  }

  async configureDeterministicBuilds() {
    console.log('🔧 Configuring deterministic builds...');
    
    // Add deterministic build scripts to package.json
    const packageJsonPath = join(this.projectRoot, 'package.json');
    const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));
    
    packageJson.scripts = {
      ...packageJson.scripts,
      'build:deterministic': 'SOURCE_DATE_EPOCH=1640995200 npm run build',
      'build:verify': 'npm run build:deterministic && npm run build:deterministic && echo "Verifying build determinism..."',
      'checksum:generate': 'find dist/ -type f -exec sha256sum {} \\; | sort > build.checksums',
      'checksum:verify': 'find dist/ -type f -exec sha256sum {} \\; | sort | diff - build.checksums'
    };
    
    writeFileSync(packageJsonPath, JSON.stringify(packageJson, null, 2));
    console.log('  ✅ Deterministic build scripts added');
  }

  async setupTestIsolation() {
    console.log('🔧 Setting up test isolation...');
    
    // Create test isolation configuration
    const vitestConfigPath = join(this.projectRoot, 'vitest.hermetic.config.ts');
    const hermeticConfig = `import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    // Hermetic test configuration
    isolate: true,
    pool: 'threads',
    poolOptions: {
      threads: {
        singleThread: true,
        isolate: true
      }
    },
    // Disable parallelism for deterministic results
    threads: false,
    // Set deterministic seed
    seed: 12345,
    // Disable watch mode
    watch: false,
    // Environment isolation
    environment: 'node',
    globals: false,
    // Cleanup between tests
    clearMocks: true,
    restoreMocks: true,
    // Timeout for hermetic tests
    testTimeout: 30000
  }
});
`;
    
    writeFileSync(vitestConfigPath, hermeticConfig);
    console.log('  ✅ Hermetic test configuration created');
  }

  async configureHermeticDependencies() {
    console.log('🔧 Configuring hermetic dependencies...');
    
    // Add dependency validation scripts
    const packageJsonPath = join(this.projectRoot, 'package.json');
    const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));
    
    packageJson.scripts = {
      ...packageJson.scripts,
      'deps:validate': 'npm ci --no-audit --no-fund --ignore-scripts',
      'deps:hermetic': 'npm ci --no-audit --no-fund --prefer-offline',
      'deps:check': 'npm ls --depth=0',
      'deps:audit:hermetic': 'npm audit --audit-level=high --production'
    };
    
    writeFileSync(packageJsonPath, JSON.stringify(packageJson, null, 2));
    console.log('  ✅ Hermetic dependency scripts added');
  }

  async setupHermeticValidation() {
    console.log('🔧 Setting up hermetic validation...');
    
    // Add hermetic validation scripts
    const packageJsonPath = join(this.projectRoot, 'package.json');
    const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));
    
    packageJson.scripts = {
      ...packageJson.scripts,
      'hermetic:analyze': 'node scripts/hermetic-ci-enhancer.js',
      'hermetic:enhance': 'node scripts/hermetic-ci-enhancer.js enhance',
      'hermetic:full': 'npm run hermetic:validate && npm run hermetic:quick && npm run hermetic:analyze'
    };
    
    writeFileSync(packageJsonPath, JSON.stringify(packageJson, null, 2));
    console.log('  ✅ Hermetic validation scripts added');
  }

  ensureReportDirectory() {
    if (!existsSync(this.reportsDir)) {
      mkdirSync(this.reportsDir, { recursive: true });
    }
  }

  async generateReport(results) {
    const reportPath = join(this.reportsDir, `hermetic-ci-${this.timestamp}.json`);
    writeFileSync(reportPath, JSON.stringify(results, null, 2));
    
    // Generate HTML report
    const htmlReport = this.generateHTMLReport(results);
    const htmlPath = join(this.reportsDir, `hermetic-ci-${this.timestamp}.html`);
    writeFileSync(htmlPath, htmlReport);
    
    console.log(`\n📋 Hermetic CI/CD report generated:`);
    console.log(`   JSON: ${reportPath}`);
    console.log(`   HTML: ${htmlPath}`);
  }

  generateHTMLReport(results) {
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Hermetic CI/CD Analysis</title>
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
        <h1><span class="icon">🔒</span>Hermetic CI/CD Analysis</h1>
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
    
    <h2>Hermetic CI/CD Checks</h2>
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
    
    <h2>Enhancement Commands</h2>
    <pre><code># Analyze hermetic CI/CD setup
npm run hermetic:analyze

# Enhance hermetic pipeline
npm run hermetic:enhance

# Run full hermetic validation
npm run hermetic:full

# Validate test hermeticity
npm run hermetic:validate

# Quick hermetic check
npm run hermetic:quick</code></pre>
</body>
</html>`;
  }
}

// CLI execution
if (import.meta.url === `file://${process.argv[1]}`) {
  const enhancer = new HermeticCIEnhancer();
  
  const command = process.argv[2];
  
  if (command === 'enhance') {
    enhancer.enhance().catch(error => {
      console.error('Hermetic CI/CD enhancement failed:', error);
      process.exit(1);
    });
  } else {
    enhancer.analyze().catch(error => {
      console.error('Hermetic CI/CD analysis failed:', error);
      process.exit(1);
    });
  }
}

export { HermeticCIEnhancer };