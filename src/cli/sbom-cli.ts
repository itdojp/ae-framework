#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import * as path from 'path';
import * as fs from 'fs/promises';
import { SBOMGenerator, type SBOMGeneratorOptions, type SBOMComponent } from '../security/sbom-generator.js';

/**
 * SBOM (Software Bill of Materials) CLI
 * Provides command-line interface for SBOM generation and management
 */
export class SBOMCLI {
  /**
   * Generate SBOM for project
   */
  async generateSBOM(options: {
    projectRoot?: string;
    output?: string;
    format?: 'json' | 'xml';
    includeDevDeps?: boolean;
    includeVulns?: boolean;
    verbose?: boolean;
  }): Promise<void> {
    const projectRoot = path.resolve(options.projectRoot || process.cwd());
    const outputPath = options.output || path.join(projectRoot, `sbom.${options.format || 'json'}`);

    try {
      if (options.verbose) {
        console.log(chalk.blue('🔍 Generating SBOM...'));
        console.log(chalk.gray(`   Project root: ${projectRoot}`));
        console.log(chalk.gray(`   Output: ${outputPath}`));
        console.log(chalk.gray(`   Format: ${options.format || 'json'}`));
        console.log(chalk.gray(`   Include dev deps: ${options.includeDevDeps || false}`));
        console.log(chalk.gray(`   Include vulnerabilities: ${options.includeVulns || false}`));
        console.log();
      }

      const generatorOptions: SBOMGeneratorOptions = {
        projectRoot,
        outputPath,
        format: options.format || 'json',
        includeDevDependencies: options.includeDevDeps || false,
        includeVulnerabilities: options.includeVulns || false,
        includeLicenses: true,
        includeHashes: true,
      };

      const generator = new SBOMGenerator(generatorOptions);
      const sbom = await generator.generate();
      
      if (options.verbose) {
        console.log(chalk.blue('📊 SBOM Summary:'));
        console.log(chalk.gray(`   Components: ${sbom.components.length}`));
        console.log(chalk.gray(`   Dependencies: ${sbom.dependencies?.length || 0}`));
        console.log(chalk.gray(`   Vulnerabilities: ${sbom.vulnerabilities?.length || 0}`));
        console.log();

        // Show component breakdown
        const componentTypes = sbom.components.reduce((acc, comp) => {
          acc[comp.type] = (acc[comp.type] || 0) + 1;
          return acc;
        }, {} as Record<string, number>);

        console.log(chalk.blue('📦 Component Types:'));
        for (const [type, count] of Object.entries(componentTypes)) {
          console.log(chalk.gray(`   ${type}: ${count}`));
        }
        console.log();
      }

      await generator.generateAndSave();

      console.log(chalk.green(`✅ SBOM generated successfully: ${outputPath}`));
      
      // Show file size
      const stats = await fs.stat(outputPath);
      const sizeKB = (stats.size / 1024).toFixed(1);
      console.log(chalk.gray(`   File size: ${sizeKB} KB`));

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to generate SBOM: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Validate existing SBOM
   */
  async validateSBOM(sbomPath: string, options: { verbose?: boolean }): Promise<void> {
    try {
      const resolvedPath = path.resolve(sbomPath);
      
      if (options.verbose) {
        console.log(chalk.blue('🔍 Validating SBOM...'));
        console.log(chalk.gray(`   File: ${resolvedPath}`));
        console.log();
      }

      const content = await fs.readFile(resolvedPath, 'utf8');
      
      // Parse based on file extension
      let sbom: any;
      if (resolvedPath.endsWith('.json')) {
        sbom = JSON.parse(content);
      } else if (resolvedPath.endsWith('.xml')) {
        // For XML validation, we'd need an XML parser
        console.log(chalk.yellow('⚠️  XML validation not implemented yet'));
        return;
      } else {
        throw new Error('Unsupported file format. Use .json or .xml');
      }

      // Basic validation
      const errors: string[] = [];
      const warnings: string[] = [];

      // Required fields
      if (!sbom.bomFormat) errors.push('Missing bomFormat');
      if (!sbom.specVersion) errors.push('Missing specVersion');
      if (!sbom.serialNumber) errors.push('Missing serialNumber');
      if (!sbom.version) errors.push('Missing version');
      if (!sbom.metadata) errors.push('Missing metadata');
      if (!sbom.components) errors.push('Missing components');

      // Metadata validation
      if (sbom.metadata) {
        if (!sbom.metadata.timestamp) warnings.push('Missing metadata.timestamp');
        if (!sbom.metadata.tools) warnings.push('Missing metadata.tools');
      }

      // Component validation
      if (sbom.components && Array.isArray(sbom.components)) {
        sbom.components.forEach((comp: any, index: number) => {
          if (!comp.name) errors.push(`Component ${index}: missing name`);
          if (!comp.version) errors.push(`Component ${index}: missing version`);
          if (!comp.type) errors.push(`Component ${index}: missing type`);
        });
      }

      // Report results
      if (errors.length > 0) {
        console.log(chalk.red('❌ SBOM validation failed:'));
        errors.forEach(error => console.log(chalk.red(`   • ${error}`)));
        safeExit(1);
      }

      if (warnings.length > 0) {
        console.log(chalk.yellow('⚠️  SBOM validation warnings:'));
        warnings.forEach(warning => console.log(chalk.yellow(`   • ${warning}`)));
      }

      console.log(chalk.green('✅ SBOM validation passed'));
      
      if (options.verbose) {
        console.log(chalk.blue('📊 SBOM Details:'));
        console.log(chalk.gray(`   Format: ${sbom.bomFormat}`));
        console.log(chalk.gray(`   Spec Version: ${sbom.specVersion}`));
        console.log(chalk.gray(`   Serial Number: ${sbom.serialNumber}`));
        console.log(chalk.gray(`   Version: ${sbom.version}`));
        console.log(chalk.gray(`   Components: ${sbom.components?.length || 0}`));
        console.log(chalk.gray(`   Dependencies: ${sbom.dependencies?.length || 0}`));
        console.log(chalk.gray(`   Vulnerabilities: ${sbom.vulnerabilities?.length || 0}`));
      }

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to validate SBOM: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Compare two SBOMs
   */
  async compareSBOMs(sbom1Path: string, sbom2Path: string, options: { verbose?: boolean }): Promise<void> {
    try {
      if (options.verbose) {
        console.log(chalk.blue('🔍 Comparing SBOMs...'));
        console.log(chalk.gray(`   SBOM 1: ${sbom1Path}`));
        console.log(chalk.gray(`   SBOM 2: ${sbom2Path}`));
        console.log();
      }

      const [content1, content2] = await Promise.all([
        fs.readFile(path.resolve(sbom1Path), 'utf8'),
        fs.readFile(path.resolve(sbom2Path), 'utf8'),
      ]);

      const sbom1 = JSON.parse(content1);
      const sbom2 = JSON.parse(content2);

      // Compare components
      const components1 = new Map<string, any>(sbom1.components?.map((c: any) => [`${c.name}@${c.version}`, c]) || []);
      const components2 = new Map<string, any>(sbom2.components?.map((c: any) => [`${c.name}@${c.version}`, c]) || []);

      const added: string[] = [];
      const removed: string[] = [];
      const changed: string[] = [];

      // Find added components
      for (const key of components2.keys()) {
        if (!components1.has(key)) {
          added.push(key);
        }
      }

      // Find removed components
      for (const key of components1.keys()) {
        if (!components2.has(key)) {
          removed.push(key);
        }
      }

      // Find changed components (same name, different version)
      const names1 = new Set(sbom1.components?.map((c: any) => c.name) || []);
      const names2 = new Set(sbom2.components?.map((c: any) => c.name) || []);
      
      for (const name of names1) {
        if (names2.has(name)) {
          const comp1 = sbom1.components?.find((c: any) => c.name === name);
          const comp2 = sbom2.components?.find((c: any) => c.name === name);
          
          if (comp1?.version !== comp2?.version) {
            changed.push(`${name}: ${comp1?.version} → ${comp2?.version}`);
          }
        }
      }

      // Report results
      console.log(chalk.blue('📊 SBOM Comparison Results:'));
      console.log();

      if (added.length > 0) {
        console.log(chalk.green(`➕ Added (${added.length}):`));
        added.forEach(comp => console.log(chalk.green(`   • ${comp}`)));
        console.log();
      }

      if (removed.length > 0) {
        console.log(chalk.red(`➖ Removed (${removed.length}):`));
        removed.forEach(comp => console.log(chalk.red(`   • ${comp}`)));
        console.log();
      }

      if (changed.length > 0) {
        console.log(chalk.yellow(`🔄 Changed (${changed.length}):`));
        changed.forEach(change => console.log(chalk.yellow(`   • ${change}`)));
        console.log();
      }

      if (added.length === 0 && removed.length === 0 && changed.length === 0) {
        console.log(chalk.green('✅ No differences found'));
      }

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to compare SBOMs: ${toMessage(error)}`));
      safeExit(1);
    }
  }

  /**
   * Generate CI/CD integration scripts
   */
  async generateCIIntegration(options: {
    ciProvider?: 'github' | 'gitlab' | 'azure' | 'jenkins';
    output?: string;
    verbose?: boolean;
  }): Promise<void> {
    const ciProvider = options.ciProvider || 'github';
    const outputPath = options.output || `./${ciProvider}-sbom-integration`;

    try {
      if (options.verbose) {
        console.log(chalk.blue('🔧 Generating CI/CD integration...'));
        console.log(chalk.gray(`   Provider: ${ciProvider}`));
        console.log(chalk.gray(`   Output: ${outputPath}`));
        console.log();
      }

      let integrationContent = '';

      switch (ciProvider) {
        case 'github':
          integrationContent = this.generateGitHubWorkflow();
          await fs.writeFile(`${outputPath}.yml`, integrationContent);
          break;
        case 'gitlab':
          integrationContent = this.generateGitLabPipeline();
          await fs.writeFile(`${outputPath}.yml`, integrationContent);
          break;
        case 'azure':
          integrationContent = this.generateAzurePipeline();
          await fs.writeFile(`${outputPath}.yml`, integrationContent);
          break;
        case 'jenkins':
          integrationContent = this.generateJenkinsfile();
          await fs.writeFile(`${outputPath}file`, integrationContent);
          break;
      }

      console.log(chalk.green(`✅ CI/CD integration generated: ${outputPath}`));
      console.log(chalk.blue('\n📋 Next steps:'));
      console.log(chalk.gray(`   1. Review the generated ${ciProvider} configuration`));
      console.log(chalk.gray(`   2. Commit the file to your repository`));
      console.log(chalk.gray(`   3. Configure any required secrets/variables`));
      console.log(chalk.gray(`   4. Test the pipeline in your CI/CD environment`));

    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to generate CI integration: ${toMessage(error)}`));
      process.exit(1);
    }
  }

  /**
   * Generate GitHub Actions workflow
   */
  private generateGitHubWorkflow(): string {
    return `name: SBOM Generation and Security Scanning

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]
  schedule:
    # Run daily at 2 AM UTC
    - cron: '0 2 * * *'

jobs:
  sbom-generation:
    runs-on: ubuntu-latest
    
    steps:
    - name: Checkout code
      uses: actions/checkout@v4
      
    - name: Setup Node.js
      uses: actions/setup-node@v4
      with:
        node-version: '18'
        cache: 'npm'
        
    - name: Install dependencies
      run: npm ci
      
    - name: Build project
      run: npm run build
      
    - name: Generate SBOM
      run: |
        npm run ae-framework sbom generate \\
          --format json \\
          --include-dev-deps \\
          --include-vulns \\
          --output sbom.json \\
          --verbose
          
    - name: Generate SBOM (XML format)
      run: |
        npm run ae-framework sbom generate \\
          --format xml \\
          --output sbom.xml \\
          --verbose
          
    - name: Validate SBOM
      run: |
        npm run ae-framework sbom validate sbom.json --verbose
        
    - name: Upload SBOM artifacts
      uses: actions/upload-artifact@v4
      with:
        name: sbom-files
        path: |
          sbom.json
          sbom.xml
        retention-days: 30
        
    - name: Compare with previous SBOM (if exists)
      if: github.event_name == 'pull_request'
      run: |
        # Download previous SBOM if available
        if [[ -f "previous-sbom.json" ]]; then
          npm run ae-framework sbom compare previous-sbom.json sbom.json --verbose
        else
          echo "No previous SBOM found for comparison"
        fi
        
    # Optional: Upload to dependency tracking service
    - name: Upload to dependency track
      if: github.ref == 'refs/heads/main'
      env:
        DT_API_KEY: \${{ secrets.DEPENDENCY_TRACK_API_KEY }}
        DT_BASE_URL: \${{ secrets.DEPENDENCY_TRACK_URL }}
      run: |
        if [[ -n "\$DT_API_KEY" && -n "\$DT_BASE_URL" ]]; then
          curl -X "PUT" "\$DT_BASE_URL/api/v1/bom" \\
            -H "X-API-Key: \$DT_API_KEY" \\
            -H "Content-Type: application/json" \\
            -d @sbom.json
        fi
        
    # Security scanning
    - name: Run npm audit
      run: npm audit --audit-level=moderate --json > audit-results.json || true
      
    - name: Upload security scan results
      uses: actions/upload-artifact@v4
      with:
        name: security-scan-results
        path: audit-results.json
        retention-days: 30
`;
  }

  /**
   * Generate GitLab CI pipeline
   */
  private generateGitLabPipeline(): string {
    return `stages:
  - build
  - security
  - deploy

variables:
  NODE_VERSION: "18"

.node_template: &node_template
  image: node:\${NODE_VERSION}
  cache:
    paths:
      - node_modules/
  before_script:
    - npm ci

build:
  <<: *node_template
  stage: build
  script:
    - npm run build
  artifacts:
    paths:
      - dist/
    expire_in: 1 hour

sbom_generation:
  <<: *node_template
  stage: security
  dependencies:
    - build
  script:
    - npm run ae-framework sbom generate --format json --include-dev-deps --include-vulns --output sbom.json --verbose
    - npm run ae-framework sbom generate --format xml --output sbom.xml --verbose
    - npm run ae-framework sbom validate sbom.json --verbose
  artifacts:
    reports:
      # GitLab dependency scanning format
      dependency_scanning: sbom.json
    paths:
      - sbom.json
      - sbom.xml
    expire_in: 30 days
  only:
    - main
    - develop
    - merge_requests

security_scan:
  <<: *node_template
  stage: security
  dependencies:
    - build
  script:
    - npm audit --audit-level=moderate --json > audit-results.json || true
  artifacts:
    reports:
      # GitLab security scanning format
      dependency_scanning: audit-results.json
    expire_in: 30 days
  allow_failure: true

dependency_tracking:
  <<: *node_template
  stage: deploy
  dependencies:
    - sbom_generation
  script:
    - |
      if [[ -n "\$DEPENDENCY_TRACK_API_KEY" && -n "\$DEPENDENCY_TRACK_URL" ]]; then
        curl -X "PUT" "\$DEPENDENCY_TRACK_URL/api/v1/bom" \\
          -H "X-API-Key: \$DEPENDENCY_TRACK_API_KEY" \\
          -H "Content-Type: application/json" \\
          -d @sbom.json
      fi
  only:
    - main
  when: manual
`;
  }

  /**
   * Generate Azure DevOps pipeline
   */
  private generateAzurePipeline(): string {
    return `trigger:
  branches:
    include:
      - main
      - develop

pr:
  branches:
    include:
      - main

schedules:
- cron: "0 2 * * *"
  displayName: Daily SBOM generation
  branches:
    include:
    - main

pool:
  vmImage: 'ubuntu-latest'

variables:
  nodeVersion: '18'

stages:
- stage: Build
  displayName: 'Build Stage'
  jobs:
  - job: Build
    displayName: 'Build Job'
    steps:
    - task: NodeTool@0
      inputs:
        versionSpec: '\$(nodeVersion)'
      displayName: 'Install Node.js'
      
    - task: Npm@1
      inputs:
        command: 'ci'
      displayName: 'npm ci'
      
    - task: Npm@1
      inputs:
        command: 'custom'
        customCommand: 'run build'
      displayName: 'npm run build'
      
- stage: Security
  displayName: 'Security and SBOM Stage'
  dependsOn: Build
  jobs:
  - job: SBOM
    displayName: 'SBOM Generation'
    steps:
    - task: NodeTool@0
      inputs:
        versionSpec: '\$(nodeVersion)'
      displayName: 'Install Node.js'
      
    - task: Npm@1
      inputs:
        command: 'ci'
      displayName: 'npm ci'
      
    - script: |
        npm run ae-framework sbom generate \\
          --format json \\
          --include-dev-deps \\
          --include-vulns \\
          --output sbom.json \\
          --verbose
      displayName: 'Generate SBOM (JSON)'
      
    - script: |
        npm run ae-framework sbom generate \\
          --format xml \\
          --output sbom.xml \\
          --verbose
      displayName: 'Generate SBOM (XML)'
      
    - script: |
        npm run ae-framework sbom validate sbom.json --verbose
      displayName: 'Validate SBOM'
      
    - task: PublishBuildArtifacts@1
      inputs:
        pathToPublish: 'sbom.json'
        artifactName: 'sbom-json'
      displayName: 'Publish SBOM JSON'
      
    - task: PublishBuildArtifacts@1
      inputs:
        pathToPublish: 'sbom.xml'
        artifactName: 'sbom-xml'
      displayName: 'Publish SBOM XML'
      
  - job: SecurityScan
    displayName: 'Security Scanning'
    steps:
    - task: NodeTool@0
      inputs:
        versionSpec: '\$(nodeVersion)'
      displayName: 'Install Node.js'
      
    - task: Npm@1
      inputs:
        command: 'ci'
      displayName: 'npm ci'
      
    - script: |
        npm audit --audit-level=moderate --json > audit-results.json || true
      displayName: 'Run npm audit'
      
    - task: PublishBuildArtifacts@1
      inputs:
        pathToPublish: 'audit-results.json'
        artifactName: 'security-scan-results'
      displayName: 'Publish Security Scan Results'
`;
  }

  /**
   * Generate Jenkinsfile
   */
  private generateJenkinsfile(): string {
    return `pipeline {
    agent any
    
    triggers {
        cron('H 2 * * *') // Daily at 2 AM
    }
    
    environment {
        NODE_VERSION = '18'
    }
    
    stages {
        stage('Setup') {
            steps {
                // Install Node.js
                nodejs(nodeJSInstallationName: 'Node \${NODE_VERSION}') {
                    sh 'node --version'
                    sh 'npm --version'
                }
            }
        }
        
        stage('Install Dependencies') {
            steps {
                nodejs(nodeJSInstallationName: 'Node \${NODE_VERSION}') {
                    sh 'npm ci'
                }
            }
        }
        
        stage('Build') {
            steps {
                nodejs(nodeJSInstallationName: 'Node \${NODE_VERSION}') {
                    sh 'npm run build'
                }
            }
        }
        
        stage('Generate SBOM') {
            parallel {
                stage('JSON SBOM') {
                    steps {
                        nodejs(nodeJSInstallationName: 'Node \${NODE_VERSION}') {
                            sh '''
                                npm run ae-framework sbom generate \\
                                  --format json \\
                                  --include-dev-deps \\
                                  --include-vulns \\
                                  --output sbom.json \\
                                  --verbose
                            '''
                        }
                    }
                }
                
                stage('XML SBOM') {
                    steps {
                        nodejs(nodeJSInstallationName: 'Node \${NODE_VERSION}') {
                            sh '''
                                npm run ae-framework sbom generate \\
                                  --format xml \\
                                  --output sbom.xml \\
                                  --verbose
                            '''
                        }
                    }
                }
            }
        }
        
        stage('Validate SBOM') {
            steps {
                nodejs(nodeJSInstallationName: 'Node \${NODE_VERSION}') {
                    sh 'npm run ae-framework sbom validate sbom.json --verbose'
                }
            }
        }
        
        stage('Security Scan') {
            steps {
                nodejs(nodeJSInstallationName: 'Node \${NODE_VERSION}') {
                    sh 'npm audit --audit-level=moderate --json > audit-results.json || true'
                }
            }
        }
        
        stage('Archive Artifacts') {
            steps {
                archiveArtifacts artifacts: 'sbom.json,sbom.xml,audit-results.json', allowEmptyArchive: true
            }
        }
        
        stage('Deploy to Dependency Track') {
            when {
                branch 'main'
            }
            steps {
                script {
                    if (env.DEPENDENCY_TRACK_API_KEY && env.DEPENDENCY_TRACK_URL) {
                        sh '''
                            curl -X "PUT" "\${DEPENDENCY_TRACK_URL}/api/v1/bom" \\
                              -H "X-API-Key: \${DEPENDENCY_TRACK_API_KEY}" \\
                              -H "Content-Type: application/json" \\
                              -d @sbom.json
                        '''
                    } else {
                        echo 'Dependency Track credentials not configured'
                    }
                }
            }
        }
    }
    
    post {
        always {
            // Clean up workspace
            cleanWs()
        }
        
        success {
            echo 'SBOM generation pipeline completed successfully'
        }
        
        failure {
            echo 'SBOM generation pipeline failed'
            // Send notifications if configured
        }
    }
}
`;
  }
}

/**
 * Create SBOM command for CLI
 */
export function createSBOMCommand(): Command {
  const command = new Command('sbom');
  command.description('Software Bill of Materials (SBOM) generation and management');
  
  const cli = new SBOMCLI();

  command
    .command('generate')
    .description('Generate SBOM for the project')
    .option('-p, --project-root <path>', 'Project root directory', process.cwd())
    .option('-o, --output <path>', 'Output file path')
    .option('-f, --format <format>', 'Output format (json|xml)', 'json')
    .option('--include-dev-deps', 'Include development dependencies')
    .option('--include-vulns', 'Include vulnerability information')
    .option('-v, --verbose', 'Verbose output')
    .action(async (options) => {
      await cli.generateSBOM(options);
    });

  command
    .command('validate <sbom-path>')
    .description('Validate an existing SBOM file')
    .option('-v, --verbose', 'Verbose output')
    .action(async (sbomPath, options) => {
      await cli.validateSBOM(sbomPath, options);
    });

  command
    .command('compare <sbom1> <sbom2>')
    .description('Compare two SBOM files')
    .option('-v, --verbose', 'Verbose output')
    .action(async (sbom1, sbom2, options) => {
      await cli.compareSBOMs(sbom1, sbom2, options);
    });

  command
    .command('ci-integration')
    .description('Generate CI/CD integration files')
    .option('-p, --ci-provider <provider>', 'CI provider (github|gitlab|azure|jenkins)', 'github')
    .option('-o, --output <path>', 'Output file path')
    .option('-v, --verbose', 'Verbose output')
    .action(async (options) => {
      await cli.generateCIIntegration(options);
    });

  return command;
}
