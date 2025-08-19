#!/usr/bin/env node
/**
 * Quality Scripts Implementation Test
 * Verifies that quality validation scripts are properly implemented and functional
 */

import { execSync, spawn } from 'child_process';
import { fileURLToPath } from 'url';
import { dirname, join } from 'path';
import { existsSync, mkdirSync } from 'fs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

async function runCommand(command, description, timeout = 30000) {
  console.log(`\n🔄 ${description}`);
  console.log(`   Command: ${command}`);
  
  return new Promise((resolve) => {
    const startTime = Date.now();
    
    try {
      const child = spawn('bash', ['-c', command], {
        stdio: ['inherit', 'pipe', 'pipe'],
        cwd: join(__dirname, '..')
      });
      
      let stdout = '';
      let stderr = '';
      
      child.stdout.on('data', (data) => {
        stdout += data.toString();
      });
      
      child.stderr.on('data', (data) => {
        stderr += data.toString();
      });
      
      const timer = setTimeout(() => {
        child.kill('SIGTERM');
        const duration = Date.now() - startTime;
        console.log(`⏱️  Timeout after ${duration}ms`);
        resolve({
          success: false,
          stdout: stdout.slice(-500), // Last 500 chars
          stderr: stderr.slice(-500),
          duration,
          error: 'Command timed out'
        });
      }, timeout);
      
      child.on('close', (code) => {
        clearTimeout(timer);
        const duration = Date.now() - startTime;
        const success = code === 0;
        
        console.log(`${success ? '✅' : '❌'} ${description} (${duration}ms)`);
        
        if (!success) {
          console.log(`   Exit code: ${code}`);
          if (stderr) {
            console.log(`   Error output: ${stderr.slice(-200)}`);
          }
        }
        
        resolve({
          success,
          stdout: stdout.slice(-1000), // Last 1000 chars
          stderr: stderr.slice(-1000),
          duration,
          exitCode: code
        });
      });
      
    } catch (error) {
      const duration = Date.now() - startTime;
      console.log(`❌ ${description} failed: ${error.message}`);
      resolve({
        success: false,
        stdout: '',
        stderr: error.message,
        duration,
        error: error.message
      });
    }
  });
}

async function testQualityScripts() {
  console.log('🔍 Quality Scripts Implementation Test');
  console.log('====================================');

  // Ensure reports directory exists
  const reportsDir = join(__dirname, '..', 'reports');
  if (!existsSync(reportsDir)) {
    mkdirSync(reportsDir, { recursive: true });
  }

  const tests = [
    {
      name: 'TDD Guard Validation',
      command: 'npm run validate-tdd',
      description: 'Test TDD guard functionality',
      timeout: 20000,
      expectedBehavior: 'Should detect files without tests and report them'
    },
    {
      name: 'Accessibility Testing',
      command: 'npm run test:a11y',
      description: 'Test accessibility validation',
      timeout: 15000,
      expectedBehavior: 'Should run accessibility tests and report violations'
    },
    {
      name: 'Coverage Testing (Fast)',
      command: 'timeout 30s npm run test:fast',
      description: 'Test coverage measurement (quick test)',
      timeout: 35000,
      expectedBehavior: 'Should measure test coverage and generate reports'
    }
  ];

  let passed = 0;
  let failed = 0;
  const results = [];

  for (const test of tests) {
    console.log(`\n=== ${test.name} ===`);
    console.log(`Expected: ${test.expectedBehavior}`);
    
    const result = await runCommand(test.command, test.description, test.timeout);
    result.testName = test.name;
    result.expectedBehavior = test.expectedBehavior;
    results.push(result);
    
    if (result.success) {
      passed++;
      console.log(`✅ ${test.name} - PASSED`);
    } else {
      failed++;
      console.log(`❌ ${test.name} - FAILED`);
      console.log(`   Error: ${result.error || 'Non-zero exit code'}`);
    }
  }

  // Additional checks
  console.log('\n=== File System Checks ===');
  
  const fileChecks = [
    { path: '.nycrc.json', description: 'NYC configuration file' },
    { path: 'jest.a11y.config.cjs', description: 'Jest accessibility configuration' },
    { path: 'policy/quality.json', description: 'Quality policy configuration' }
  ];

  for (const check of fileChecks) {
    const fullPath = join(__dirname, '..', check.path);
    const exists = existsSync(fullPath);
    console.log(`${exists ? '✅' : '❌'} ${check.description}: ${exists ? 'EXISTS' : 'MISSING'}`);
    
    if (exists) {
      passed++;
    } else {
      failed++;
    }
  }

  // Summary
  console.log('\n=== Test Results Summary ===');
  console.log(`✅ Passed: ${passed}`);
  console.log(`❌ Failed: ${failed}`);
  console.log(`📊 Total: ${passed + failed}`);

  // Detailed results
  console.log('\n=== Detailed Results ===');
  for (const result of results) {
    console.log(`\n📋 ${result.testName}:`);
    console.log(`   Status: ${result.success ? 'PASSED' : 'FAILED'}`);
    console.log(`   Duration: ${result.duration}ms`);
    console.log(`   Exit Code: ${result.exitCode || 'N/A'}`);
    
    if (!result.success && result.stderr) {
      console.log(`   Error Preview: ${result.stderr.slice(0, 200)}...`);
    }
    
    if (result.stdout && result.stdout.length > 0) {
      console.log(`   Output Preview: ${result.stdout.slice(0, 200)}...`);
    }
  }

  const success = failed === 0;
  
  console.log(`\n${success ? '🎉' : '💥'} Quality Scripts ${success ? 'Working Correctly' : 'Have Issues'}!`);
  
  if (!success) {
    console.log('\n📋 Issues Found:');
    if (failed > passed) {
      console.log('• Majority of quality scripts are failing');
      console.log('• Check dependency installation and configuration');
    }
    console.log('• Review error messages above for specific fixes needed');
    console.log('• Ensure all required dependencies are installed');
    console.log('• Verify configuration files are properly formatted');
  } else {
    console.log('\n📋 Quality Script Benefits:');
    console.log('• TDD guard validates test coverage gaps');
    console.log('• Accessibility testing ensures WCAG compliance');
    console.log('• Coverage measurement tracks code quality');
    console.log('• All scripts integrated with centralized quality policy');
  }

  return success;
}

// Run the test
testQualityScripts()
  .then(success => {
    console.log(`\n🏁 Test completed. Success: ${success}`);
    process.exit(success ? 0 : 1);
  })
  .catch(error => {
    console.error('💥 Test crashed:', error);
    process.exit(1);
  });