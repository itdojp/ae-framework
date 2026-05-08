/**
 * Security CLI commands for the AE-Framework
 * Provides commands to test and manage security headers
 */

import path from 'node:path';
import { tmpdir } from 'node:os';
import { existsSync, realpathSync } from 'node:fs';
import { Command } from 'commander';
import chalk from 'chalk';
import { createServer } from '../api/server.js';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import { getSecurityConfiguration, securityConfigurations } from '../api/middleware/security-headers.js';
import { generateSecurityCodeMap } from '../security/assurance/code-map.js';
import { extractSecurityClaimsFromSpec } from '../security/assurance/claim-extractor.js';
import { importSpecaLikeSecurityArtifacts } from '../security/assurance/speca-import.js';
import { generateSecurityProofAudit } from '../security/assurance/proof-audit.js';
import { generateSecurityThreeGateReview } from '../security/assurance/three-gate-review.js';
import { normalizeArtifactPath } from '../utils/path-normalization.js';


function pathHasTraversalSegment(value: string): boolean {
  return value
    .replace(/\\/g, '/')
    .split('/')
    .some((segment) => segment === '..');
}

function isInsideDirectory(parentDir: string, candidatePath: string): boolean {
  const relative = path.relative(parentDir, candidatePath);
  return relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative));
}

function nearestExistingPath(candidatePath: string): string {
  let current = candidatePath;
  while (!existsSync(current)) {
    const parent = path.dirname(current);
    if (parent === current) {
      return current;
    }
    current = parent;
  }
  return current;
}

function resolveThroughExistingParent(candidatePath: string): string {
  const nearestExisting = nearestExistingPath(candidatePath);
  const nearestRealPath = realpathSync.native(nearestExisting);
  const unresolvedSuffix = path.relative(nearestExisting, candidatePath);
  return unresolvedSuffix ? path.resolve(nearestRealPath, unresolvedSuffix) : nearestRealPath;
}

function assertSafeSecurityOutputPath(value: string, optionName = '--out'): string {
  const raw = String(value || '').trim();
  if (!raw) {
    throw new Error(`Unsafe ${optionName} path: output path must not be empty.`);
  }
  if (pathHasTraversalSegment(raw)) {
    throw new Error(`Unsafe ${optionName} path: path traversal segments are not allowed.`);
  }

  const resolved = path.resolve(raw);
  const allowedRoots = [process.cwd(), tmpdir()].map((entry) => path.resolve(entry));
  if (!allowedRoots.some((root) => isInsideDirectory(root, resolved))) {
    throw new Error(`Unsafe ${optionName} path: absolute output paths must stay under the current working directory or the OS temp directory.`);
  }
  const realResolved = resolveThroughExistingParent(resolved);
  const realAllowedRoots = allowedRoots.map((root) => realpathSync.native(root));
  if (!realAllowedRoots.some((root) => isInsideDirectory(root, realResolved))) {
    throw new Error(`Unsafe ${optionName} path: existing symlink segments must not resolve outside the current working directory or the OS temp directory.`);
  }
  return raw;
}

function displayArtifactPath(value: string): string {
  return normalizeArtifactPath(value, { repoRoot: process.cwd() }) ?? value.replace(/\\/g, '/');
}

export function createSecurityCommand(): Command {
  const security = new Command('security');
  security.description('Security management commands');

  security
    .command('review')
    .description('Classify candidate security findings through Dead Code, Trust Boundary, and Scope gates')
    .requiredOption('-f, --findings <file>', 'security-finding/v1 JSON artifact')
    .requiredOption('-s, --scope <file>', 'security-audit-scope/v1 JSON artifact')
    .requiredOption('-m, --code-map <file>', 'security-code-map/v1 JSON artifact')
    .requiredOption('-o, --out <path>', 'Output directory or security-review JSON path')
    .option('--entrypoint-map <file>', 'Optional security-entrypoint-map/v1 JSON artifact for Trust Boundary evidence')
    .option('--claims <file>', 'Optional security-claim/v1 JSON artifact for claim type-aware review')
    .option('--generated-at <iso-date>', 'Deterministic generatedAt timestamp for reproducible review artifacts')
    .option('--no-validate', 'Skip schema validation for input and generated artifacts')
    .action(async (options) => {
      try {
        const outPath = assertSafeSecurityOutputPath(options.out);
        const result = await generateSecurityThreeGateReview(options.findings, options.scope, options.codeMap, outPath, {
          generatedAt: options.generatedAt,
          entrypointMapPath: options.entrypointMap,
          claimsPath: options.claims,
          validate: options.validate,
        });

        console.log(chalk.green('✅ Security three-gate review completed'));
        console.log(`Reviews: ${result.review.summary.totalReviews}`);
        console.log(`Needs human review: ${result.review.summary.byResult.needsHumanReview}`);
        console.log(`Rejected: ${result.review.summary.byResult.rejected}`);
        console.log(`Out of scope: ${result.review.summary.byResult.outOfScope}`);
        console.log(`Warnings: ${result.warnings.length}`);
        console.log(`Output: ${displayArtifactPath(result.outputPaths.review)}`);
        console.log(`Summary: ${displayArtifactPath(result.outputPaths.summaryMarkdown)}`);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Security three-gate review failed: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  security
    .command('audit')
    .description('Generate proof-attempt audit tasks and fixture-backed candidate security findings')
    .requiredOption('-c, --claims <file>', 'security-claim/v1 JSON artifact')
    .requiredOption('-m, --code-map <file>', 'security-code-map/v1 JSON artifact')
    .requiredOption('-s, --scope <file>', 'security-audit-scope/v1 JSON artifact')
    .requiredOption('-o, --out <path>', 'Output directory or security-findings JSON path')
    .option('-r, --response-fixture <file>', 'Fixture response JSON to simulate proof-attempt results and emit security-finding/v1')
    .option('--generated-at <iso-date>', 'Deterministic generatedAt timestamp for reproducible audit artifacts')
    .option('--no-validate', 'Skip schema validation for input and generated artifacts')
    .action(async (options) => {
      try {
        const outPath = assertSafeSecurityOutputPath(options.out);
        const result = await generateSecurityProofAudit(options.claims, options.codeMap, options.scope, outPath, {
          generatedAt: options.generatedAt,
          validate: options.validate,
          responseFixture: options.responseFixture,
        });

        console.log(chalk.green('✅ Security proof-attempt audit completed'));
        console.log(`Audit tasks: ${result.taskBundle.summary.totalTasks}`);
        console.log(`Ready tasks: ${result.taskBundle.summary.readyTasks}`);
        console.log(`Blocked tasks: ${result.taskBundle.summary.blockedTasks}`);
        console.log(`Findings: ${result.findings?.summary.totalFindings ?? 0}`);
        console.log(`No-finding responses: ${result.responseSummary.noFindingResponses}`);
        console.log(`Warnings: ${result.warnings.length}`);
        console.log(`Tasks: ${displayArtifactPath(result.outputPaths.tasks)}`);
        if (result.findings && result.outputPaths.findings) {
          console.log(`Findings output: ${displayArtifactPath(result.outputPaths.findings)}`);
        } else {
          console.log('Findings output: not generated (dry-run or all responses were no-finding)');
        }
        console.log(`Summary: ${displayArtifactPath(result.outputPaths.summaryMarkdown)}`);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Security proof-attempt audit failed: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  security
    .command('map-code')
    .description('Map security-claim/v1 entries to candidate source locations before proof-attempt audit')
    .requiredOption('-c, --claims <file>', 'security-claim/v1 JSON artifact')
    .requiredOption('-s, --scope <file>', 'security-audit-scope/v1 JSON artifact with in/out-of-scope globs')
    .requiredOption('-t, --target <dir>', 'Target repository or fixture directory to scan')
    .requiredOption('-o, --out <path>', 'Output JSON path or directory for security-code-map artifacts')
    .option('--symbol-index <file>', 'Optional symbol-index/v1 JSON artifact to prioritize claim-to-code mapping')
    .option('--generated-at <iso-date>', 'Deterministic generatedAt timestamp for reproducible mapping')
    .option('--no-validate', 'Skip schema validation for input and generated artifacts')
    .action(async (options) => {
      try {
        const outPath = assertSafeSecurityOutputPath(options.out);
        const result = await generateSecurityCodeMap(options.claims, options.scope, options.target, outPath, {
          generatedAt: options.generatedAt,
          symbolIndexPath: options.symbolIndex,
          validate: options.validate,
        });

        console.log(chalk.green('✅ Security code-map generation completed'));
        console.log(`Claims: ${result.codeMap.summary.totalClaims}`);
        console.log(`Mapped claims: ${result.codeMap.summary.mappedClaims}`);
        console.log(`Candidate locations: ${result.codeMap.summary.totalCandidateLocations}`);
        if (result.codeMap.summary.symbolIndex) {
          console.log(`Symbol index: ${displayArtifactPath(result.codeMap.summary.symbolIndex.input)}`);
          console.log(`Symbol-index fallback claims: ${result.codeMap.summary.symbolIndex.fallbackClaims}`);
        }
        console.log(`Warnings: ${result.warnings.length}`);
        console.log(`Output: ${displayArtifactPath(result.outputPaths.codeMap)}`);
        console.log(`Summary: ${displayArtifactPath(result.outputPaths.summaryMarkdown)}`);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Security code-map generation failed: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  security
    .command('extract-claims')
    .description('Extract explicit SEC-CLAIM blocks from a Markdown specification into security-claim/v1')
    .requiredOption('-s, --spec <file>', 'Markdown specification containing SEC-CLAIM blocks')
    .requiredOption('-o, --out <path>', 'Output JSON path or directory for security-claim artifacts')
    .option('--generated-at <iso-date>', 'Deterministic generatedAt timestamp for reproducible extraction')
    .option('--no-validate', 'Skip schema validation for generated artifacts')
    .action(async (options) => {
      try {
        const outPath = assertSafeSecurityOutputPath(options.out);
        const result = await extractSecurityClaimsFromSpec(options.spec, outPath, {
          generatedAt: options.generatedAt,
          validate: options.validate,
        });

        console.log(chalk.green('✅ Security claims extraction completed'));
        console.log(`Claims: ${result.claims.claims.length}`);
        console.log(`Warnings: ${result.warnings.length}`);
        console.log(`Output: ${displayArtifactPath(result.outputPaths.claims)}`);
        console.log(`Summary: ${displayArtifactPath(result.outputPaths.summaryMarkdown)}`);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Security claims extraction failed: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  security
    .command('import-speca')
    .description('Import SPECA-like security audit output into ae-framework security assurance artifacts')
    .requiredOption('-i, --input <dir>', 'Directory containing SPECA-like JSON outputs')
    .requiredOption('-o, --out <dir>', 'Output directory for ae-framework security artifacts')
    .option('--generated-at <iso-date>', 'Deterministic generatedAt timestamp for reproducible imports')
    .option('--no-validate', 'Skip schema validation for generated artifacts')
    .action(async (options) => {
      try {
        const outPath = assertSafeSecurityOutputPath(options.out);
        const result = await importSpecaLikeSecurityArtifacts(options.input, outPath, {
          generatedAt: options.generatedAt,
          validate: options.validate,
        });

        console.log(chalk.green('✅ SPECA-compatible security import completed'));
        console.log(`Claims: ${result.artifacts.claims.claims.length}`);
        console.log(`Threats: ${result.artifacts.threatModel.threats.length}`);
        console.log(`Findings: ${result.artifacts.findings.findings.length}`);
        console.log(`Reviews: ${result.artifacts.review.reviews.length}`);
        console.log(`Warnings: ${result.warnings.length}`);
        console.log(`Summary: ${displayArtifactPath(result.outputPaths.summaryMarkdown)}`);
      } catch (error: unknown) {
        console.error(chalk.red(`❌ SPECA-compatible security import failed: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Test security headers command
  security
    .command('test-headers')
    .description('Test security headers configuration')
    .option('-p, --port <port>', 'Port to run test server on', '3000')
    .option('-e, --env <environment>', 'Environment configuration to test', 'development')
    .action(async (options) => {
      try {
        console.log('🔒 Testing security headers configuration...\n');
        
        const config = getSecurityConfiguration(options.env);
        console.log(`Environment: ${options.env}`);
        console.log(`Configuration:`, JSON.stringify(config, null, 2));
        
        console.log('\n🚀 Starting test server...');
        const app = await createServer();
        
        await app.listen({ port: parseInt(options.port), host: '0.0.0.0' });
        console.log(`✅ Test server running on http://localhost:${options.port}`);
        console.log('\nTest endpoints:');
        console.log(`  - GET  http://localhost:${options.port}/health`);
        console.log(`  - POST http://localhost:${options.port}/reservations`);
        console.log('\nPress Ctrl+C to stop the server');
        
        // Handle graceful shutdown
        process.on('SIGINT', async () => {
          console.log('\n\n🛑 Shutting down test server...');
          await app.close();
          safeExit(0);
        });
        
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error starting test server: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Check headers command
  security
    .command('check-headers')
    .description('Check security headers on a running server')
    .option('-u, --url <url>', 'URL to check', 'http://localhost:3000/health')
    .option('-v, --verbose', 'Verbose output')
    .action(async (options) => {
      try {
        console.log('🔍 Checking security headers...\n');
        
        const response = await fetch(options.url);
        const headers = response.headers;
        
        console.log(`URL: ${options.url}`);
        console.log(`Status: ${response.status} ${response.statusText}\n`);
        
        // Check for security headers
        const securityHeaders = [
          'content-security-policy',
          'x-frame-options',
          'x-content-type-options',
          'referrer-policy',
          'strict-transport-security',
          'x-xss-protection',
          'permissions-policy'
        ];
        
        console.log('Security Headers Analysis:');
        console.log('='.repeat(50));
        
        let secureHeadersCount = 0;
        
        for (const headerName of securityHeaders) {
          const headerValue = headers.get(headerName);
          if (headerValue) {
            console.log(`✅ ${headerName}: ${headerValue}`);
            secureHeadersCount++;
          } else {
            console.log(`❌ ${headerName}: Not present`);
          }
        }
        
        console.log('\n' + '='.repeat(50));
        console.log(`Security Score: ${secureHeadersCount}/${securityHeaders.length} headers present`);
        
        // Check for headers that should be removed
        const unwantedHeaders = ['server', 'x-powered-by'];
        const foundUnwantedHeaders = unwantedHeaders.filter(h => headers.get(h));
        
        if (foundUnwantedHeaders.length > 0) {
          console.log('\n⚠️  Unwanted headers found:');
          foundUnwantedHeaders.forEach(h => {
            console.log(`   - ${h}: ${headers.get(h)}`);
          });
        } else {
          console.log('\n✅ No unwanted server identification headers found');
        }
        
        if (options.verbose) {
          console.log('\nAll Response Headers:');
          console.log('-'.repeat(30));
          headers.forEach((value, name) => {
            console.log(`${name}: ${value}`);
          });
        }
        
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error checking headers: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Show configuration command
  security
    .command('show-config')
    .description('Show security configuration for different environments')
    .option('-e, --env <environment>', 'Show specific environment configuration')
    .action(async (options) => {
      console.log('🔒 Security Headers Configuration\n');
      
      if (options.env) {
        const config = getSecurityConfiguration(options.env);
        console.log(`Environment: ${options.env}`);
        console.log(JSON.stringify(config, null, 2));
      } else {
        console.log('Available environments:\n');
        Object.entries(securityConfigurations).forEach(([env, config]) => {
          console.log(`${env.toUpperCase()}:`);
          console.log(JSON.stringify(config, null, 2));
          console.log('');
        });
      }
    });

  // Scan command for external URLs
  security
    .command('scan')
    .description('Scan external URL for security headers')
    .argument('<url>', 'URL to scan')
    .option('-t, --timeout <ms>', 'Request timeout in milliseconds', '5000')
    .action(async (url, options) => {
      try {
        console.log(`🔍 Scanning ${url} for security headers...\n`);
        
        const controller = new AbortController();
        let timeoutMs = parseInt(options.timeout, 10);
        if (!Number.isFinite(timeoutMs) || timeoutMs <= 0) {
          timeoutMs = 5000;
        }
        const timeoutId = setTimeout(() => controller.abort(), timeoutMs);
        
        const response = await fetch(url, {
          signal: controller.signal,
          headers: {
            'User-Agent': 'AE-Framework Security Scanner'
          }
        });
        
        clearTimeout(timeoutId);
        
        console.log(`Status: ${response.status} ${response.statusText}`);
        console.log(`Server: ${response.headers.get('server') || 'Not disclosed'}\n`);
        
        // Security headers analysis
        const securityAnalysis = [
          {
            name: 'Content Security Policy',
            header: 'content-security-policy',
            critical: true,
            description: 'Prevents XSS attacks by controlling resource loading'
          },
          {
            name: 'X-Frame-Options',
            header: 'x-frame-options',
            critical: true,
            description: 'Prevents clickjacking attacks'
          },
          {
            name: 'X-Content-Type-Options',
            header: 'x-content-type-options',
            critical: false,
            description: 'Prevents MIME type sniffing'
          },
          {
            name: 'Strict-Transport-Security',
            header: 'strict-transport-security',
            critical: true,
            description: 'Enforces HTTPS connections'
          },
          {
            name: 'Referrer-Policy',
            header: 'referrer-policy',
            critical: false,
            description: 'Controls referrer information leakage'
          },
          {
            name: 'Permissions-Policy',
            header: 'permissions-policy',
            critical: false,
            description: 'Controls browser feature access'
          }
        ];
        
        let criticalMissing = 0;
        let totalMissing = 0;
        
        console.log('Security Headers Report:');
        console.log('='.repeat(60));
        
        for (const { name, header, critical, description } of securityAnalysis) {
          const value = response.headers.get(header);
          if (value) {
            console.log(`✅ ${name}: Present`);
            console.log(`   Value: ${value}`);
          } else {
            const severity = critical ? '🔴 CRITICAL' : '🟡 OPTIONAL';
            console.log(`❌ ${name}: Missing ${severity}`);
            console.log(`   Impact: ${description}`);
            if (critical) criticalMissing++;
            totalMissing++;
          }
          console.log('');
        }
        
        console.log('='.repeat(60));
        console.log(`Summary: ${securityAnalysis.length - totalMissing}/${securityAnalysis.length} headers present`);
        if (criticalMissing > 0) {
          console.log(`🔴 ${criticalMissing} critical security headers missing!`);
        } else {
          console.log('✅ All critical security headers present');
        }
        
      } catch (error) {
        if (error instanceof Error && error.name === 'AbortError') {
          console.error(chalk.red('❌ Request timed out'));
        } else {
          console.error(chalk.red(`❌ Error scanning URL: ${toMessage(error)}`));
        }
        safeExit(1);
      }
    });

  return security;
}

export default createSecurityCommand;
