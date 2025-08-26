import { writeFile, mkdir, access, constants, readFile } from 'node:fs/promises';
import { exec } from 'node:child_process';
import { promisify } from 'node:util';
import path from 'node:path';
import { run } from '../../core/exec.js';
import { err, ok, isErr, type Result } from '../../core/result.js';
import type { AppError } from '../../core/errors.js';

const execAsync = promisify(exec);

async function hasBin(bin: string): Promise<boolean> {
  // a) Check node_modules/.bin/<bin>
  try {
    await access(path.join('node_modules', '.bin', bin), constants.F_OK);
    return true;
  } catch {
    // Continue to next check
  }

  // b) Check PATH environment variable
  const pathEnv = process.env.PATH || '';
  const pathSeparator = process.platform === 'win32' ? ';' : ':';
  const paths = pathEnv.split(pathSeparator);
  
  for (const binPath of paths) {
    if (!binPath) continue;
    try {
      const binFile = process.platform === 'win32' 
        ? path.join(binPath, `${bin}.exe`)
        : path.join(binPath, bin);
      await access(binFile, constants.F_OK);
      return true;
    } catch {
      // Continue to next path
    }
  }

  // c) Try command -v as last resort
  try {
    await execAsync(`command -v ${bin}`);
    return true;
  } catch {
    return false;
  }
}

async function hasFile(file: string): Promise<boolean> {
  try {
    await access(file, constants.F_OK);
    return true;
  } catch {
    return false;
  }
}

async function hasScript(scriptName: string): Promise<boolean> {
  try {
    const packageJsonContent = await readFile('package.json', 'utf8');
    const packageJson = JSON.parse(packageJsonContent);
    return packageJson.scripts && typeof packageJson.scripts[scriptName] === 'string';
  } catch {
    return false;
  }
}

export async function verifyRun(): Promise<Result<{ logs: string[]; duration: string }, AppError>> {
  console.log('[ae][verify] Starting verification pipeline...');
  await mkdir('artifacts', { recursive: true });
  
  const logs: string[] = [];
  let success = true;
  const startTime = new Date();

  async function step(name: string, cmd: string, args: string[], env?: Record<string, string>): Promise<void> {
    logs.push(`## ${name}\n\`\`\`bash\n${[cmd, ...args].join(' ')}\n\`\`\``);
    console.log(`[ae][verify] ${name} start`);
    
    const result = await run(name, cmd, args, {
      stdio: 'inherit',
      env: env ? { ...process.env, ...env } : process.env,
      timeout: 120000  // 120 second timeout per step
    });
    
    if (result.ok) {
      logs.push(`✅ ${name}: OK`);
      console.log(`[ae][verify] ${name} end: OK`);
    } else if (isErr(result)) {
      success = false;
      const errorMsg = 'detail' in result.error ? result.error.detail : result.error.code;
      logs.push(`❌ ${name}: FAILED (${errorMsg ?? 'unknown error'})`);
      console.log(`[ae][verify] ${name} end: FAILED`);
    }
  }

  async function softStep(name: string, cmd: string, args: string[], env?: Record<string, string>) {
    logs.push(`## ${name}\n\`\`\`bash\n${[cmd, ...args].join(' ')}\n\`\`\``);
    console.log(`[ae][verify] ${name} start`);
    
    const result = await run(name, cmd, args, {
      stdio: 'inherit',
      timeout: 120000,  // 120 second timeout per step
      env: env ? { ...process.env, ...env } : process.env
    });
    
    if (result.ok) {
      logs.push(`✅ ${name}: OK`);
      console.log(`[ae][verify] ${name} end: OK`);
    } else if (isErr(result)) {
      // Don't set success = false for soft steps
      const errorMsg = 'detail' in result.error ? result.error.detail : result.error.code;
      logs.push(`⚠️  ${name}: INFO (${errorMsg ?? 'unknown error'})`);
      console.log(`[ae][verify] ${name} end: INFO`);
    }
  }

  const isStrict = process.env.AE_TYPES_STRICT === '1';
  
  try {
    // 1) TypeScript type check (prioritize scoped config)
    try {
      if (await hasBin('tsc')) {
        const tscProject = process.env.AE_TSC_PROJECT;
        let args: string[];
        
        if (tscProject) {
          // Use explicit project specified by AE_TSC_PROJECT
          args = ['-p', tscProject];
          console.log(`[ae][verify] TypeScript Types: using project ${tscProject}`);
        } else if (await hasFile('tsconfig.verify.json')) {
          args = ['-p', 'tsconfig.verify.json'];
        } else if (await hasFile('tsconfig.build.json')) {
          args = ['-p', 'tsconfig.build.json'];
        } else {
          args = ['--noEmit'];
        }
        
        await step('TypeScript Types', 'tsc', args);
      } else {
        logs.push('## TypeScript Types\nℹ️  Skipped (tsc not available)');
        console.log('[ae][verify] TypeScript Types: SKIPPED (tsc not available)');
      }
    } catch (error) {
      success = false;
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## TypeScript Types\n❌ FAILED (error: ${errorMsg})`);
      console.log(`[ae][verify] TypeScript Types: FAILED (error: ${errorMsg})`);
    }

    // 2) ESLint (check for flat config, graceful skip if missing)
    try {
      if (await hasBin('eslint')) {
        if (await hasFile('eslint.config.js') || await hasFile('eslint.config.mjs') || await hasFile('eslint.config.ts')) {
          const lintScope = process.env.AE_LINT_SCOPE;
          let args: string[];
          
          if (lintScope) {
            // Use scoped path specified by AE_LINT_SCOPE
            args = [lintScope];
            console.log(`[ae][verify] ESLint: using scope ${lintScope}`);
          } else {
            args = ['.'];
          }
          
          await step('ESLint', 'eslint', args);
        } else {
          logs.push('## ESLint\n⚠️  WARN: No flat config (eslint.config.js) found - skipped');
          console.log('[ae][verify] ESLint: WARN (no flat config found, skipped)');
        }
      } else {
        logs.push('## ESLint\nℹ️  Skipped (eslint not available)');
        console.log('[ae][verify] ESLint: SKIPPED (eslint not available)');
      }
    } catch (error) {
      success = false;
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## ESLint\n❌ FAILED (error: ${errorMsg})`);
      console.log(`[ae][verify] ESLint: FAILED (error: ${errorMsg})`);
    }

    // 3) QA metrics
    try {
      if (await hasFile('dist/cli.js')) {
        await step('QA Metrics', 'node', ['dist/cli.js', 'qa']);
      } else {
        logs.push('## QA Metrics\nℹ️  Skipped (ae CLI not built)');
        console.log('[ae][verify] QA Metrics: SKIPPED (ae CLI not built)');
      }
    } catch (error) {
      success = false;
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## QA Metrics\n❌ FAILED (error: ${errorMsg})`);
      console.log(`[ae][verify] QA Metrics: FAILED (error: ${errorMsg})`);
    }

    // 4) Benchmarks (with deterministic seed)
    try {
      if (await hasFile('dist/cli.js')) {
        await step('Benchmarks', 'node', ['dist/cli.js', 'bench'], { AE_SEED: '123' });
      } else {
        logs.push('## Benchmarks\nℹ️  Skipped (ae CLI not built)');
        console.log('[ae][verify] Benchmarks: SKIPPED (ae CLI not built)');
      }
    } catch (error) {
      success = false;
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## Benchmarks\n❌ FAILED (error: ${errorMsg})`);
      console.log(`[ae][verify] Benchmarks: FAILED (error: ${errorMsg})`);
    }

    // 5) Type tests (non-blocking)
    try {
      if (await hasBin('tsd')) {
        await softStep('Type Tests', 'tsd', []);
      } else {
        logs.push('## Type Tests\nℹ️  Skipped (tsd not available)');
        console.log('[ae][verify] Type Tests: SKIPPED (tsd not available)');
      }
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## Type Tests\n⚠️  INFO: ${errorMsg}`);
      console.log(`[ae][verify] Type Tests: INFO (${errorMsg})`);
    }

    // 6) Type coverage (non-blocking)
    try {
      if (await hasBin('type-coverage')) {
        await softStep('Type Coverage', 'type-coverage', ['-p', 'tsconfig.verify.json', '--ignore-catch']);
      } else {
        logs.push('## Type Coverage\nℹ️  Skipped (type-coverage not available)');
        console.log('[ae][verify] Type Coverage: SKIPPED (type-coverage not available)');
      }
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## Type Coverage\n⚠️  INFO: ${errorMsg}`);
      console.log(`[ae][verify] Type Coverage: INFO (${errorMsg})`);
    }

    // 7) API type snapshot check (non-blocking)
    try {
      if (await hasFile('pnpm-lock.yaml') || await hasFile('package-lock.json')) {
        await softStep('API Type Check', 'pnpm', ['api:check']);
      } else {
        logs.push('## API Type Check\nℹ️  Skipped (no package manager lockfile found)');
        console.log('[ae][verify] API Type Check: SKIPPED (no lockfile found)');
      }
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## API Type Check\n⚠️  INFO: ${errorMsg}`);
      console.log(`[ae][verify] API Type Check: INFO (${errorMsg})`);
    }

    // 8) Strict TypeScript verification (strict mode only)
    try {
      if (await hasFile('tsconfig.verify.json')) {
        const stepFn = isStrict ? step : softStep;
        await stepFn('Strict TypeScript Check', 'tsc', ['-p', 'tsconfig.verify.json', '--noEmit']);
      } else {
        logs.push('## Strict TypeScript Check\nℹ️  Skipped (tsconfig.verify.json not found)');
        console.log('[ae][verify] Strict TypeScript Check: SKIPPED (no tsconfig.verify.json)');
      }
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      if (isStrict) {
        success = false;
        logs.push(`## Strict TypeScript Check\n❌ FAILED: ${errorMsg}`);
        console.log(`[ae][verify] Strict TypeScript Check: FAILED (${errorMsg})`);
      } else {
        logs.push(`## Strict TypeScript Check\n⚠️  INFO: ${errorMsg}`);
        console.log(`[ae][verify] Strict TypeScript Check: INFO (${errorMsg})`);
      }
    }

    // 9) Strict ESLint verification (type-checked)
    try {
      if (await hasBin('eslint')) {
        const stepFn = isStrict ? step : softStep;
        await stepFn('Strict ESLint Check', 'eslint', ['.']);
      } else {
        logs.push('## Strict ESLint Check\nℹ️  Skipped (eslint not available)');
        console.log('[ae][verify] Strict ESLint Check: SKIPPED (eslint not available)');
      }
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      if (isStrict) {
        success = false;
        logs.push(`## Strict ESLint Check\n❌ FAILED: ${errorMsg}`);
        console.log(`[ae][verify] Strict ESLint Check: FAILED (${errorMsg})`);
      } else {
        logs.push(`## Strict ESLint Check\n⚠️  INFO: ${errorMsg}`);
        console.log(`[ae][verify] Strict ESLint Check: INFO (${errorMsg})`);
      }
    }

    // 10) Type tests (tsd)
    try {
      if (await hasScript('test:types')) {
        const stepFn = isStrict ? step : softStep;
        await stepFn('Type Tests (tsd)', 'pnpm', ['run', 'test:types']);
      } else {
        logs.push('## Type Tests (tsd)\nℹ️  Skipped (test:types script not found)');
        console.log('[ae][verify] Type Tests (tsd): SKIPPED (test:types script not found)');
      }
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      if (isStrict) {
        success = false;
        logs.push(`## Type Tests (tsd)\n❌ FAILED: ${errorMsg}`);
        console.log(`[ae][verify] Type Tests (tsd): FAILED (${errorMsg})`);
      } else {
        logs.push(`## Type Tests (tsd)\n⚠️  INFO: ${errorMsg}`);
        console.log(`[ae][verify] Type Tests (tsd): INFO (${errorMsg})`);
      }
    }

    // 11) API snapshot verification (strict)
    try {
      const hasApiCheck = await hasScript('api:check');
      const stepFn = isStrict ? step : softStep;
      if (hasApiCheck) {
        await stepFn('API Snapshot Check', 'pnpm', ['run', 'api:check']);
      } else {
        logs.push('## API Snapshot Check\nℹ️  Skipped (api:check script not found in package.json)');
        console.log('[ae][verify] API Snapshot Check: SKIPPED (api:check script not found in package.json)');
      }
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      if (isStrict) {
        success = false;
        logs.push(`## API Snapshot Check\n❌ FAILED: ${errorMsg}`);
        console.log(`[ae][verify] API Snapshot Check: FAILED (${errorMsg})`);
      } else {
        logs.push(`## API Snapshot Check\n⚠️  INFO: ${errorMsg}`);
        console.log(`[ae][verify] API Snapshot Check: INFO (${errorMsg})`);
      }
    }

    // 12) TypeScript Comment Policy check
    try {
      const stepFn = isStrict ? step : softStep;
      await stepFn('TypeScript Comment Policy', 'node', ['scripts/ci/check-expect-error.mjs']);
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      if (isStrict) {
        success = false;
        logs.push(`## TypeScript Comment Policy\n❌ FAILED: ${errorMsg}`);
        console.log(`[ae][verify] TypeScript Comment Policy: FAILED (${errorMsg})`);
      } else {
        logs.push(`## TypeScript Comment Policy\n⚠️  INFO: ${errorMsg}`);
        console.log(`[ae][verify] TypeScript Comment Policy: INFO (${errorMsg})`);
      }
    }

    // 13) API Extractor report generation
    try {
      const stepFn = isStrict ? step : softStep;
      await stepFn('API Extractor Report', 'pnpm', ['run', 'api:emit']);
      await stepFn('API Extractor Report', 'pnpm', ['run', 'api:report']);
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      if (isStrict) {
        success = false;
        logs.push(`## API Extractor Report\n❌ FAILED: ${errorMsg}`);
        console.log(`[ae][verify] API Extractor Report: FAILED (${errorMsg})`);
      } else {
        logs.push(`## API Extractor Report\n⚠️  INFO: ${errorMsg}`);
        console.log(`[ae][verify] API Extractor Report: INFO (${errorMsg})`);
      }
    }

    // 14) API Breaking Change Detection
    try {
      const stepFn = isStrict ? step : softStep;
      await stepFn('API Breaking Changes', 'pnpm', ['run', 'api:diff']);
    } catch (error) {
      const errorMsg = error instanceof Error ? error.message : String(error);
      if (isStrict) {
        success = false;
        logs.push(`## API Breaking Changes\n❌ FAILED: ${errorMsg}`);
        console.log(`[ae][verify] API Breaking Changes: FAILED (${errorMsg})`);
      } else {
        logs.push(`## API Breaking Changes\n⚠️  INFO: ${errorMsg}`);
        console.log(`[ae][verify] API Breaking Changes: INFO (${errorMsg})`);
      }
    }

  } catch (unexpectedError) {
    success = false;
    const errorMsg = unexpectedError instanceof Error ? unexpectedError.message : String(unexpectedError);
    logs.push(`## Unexpected Error\n❌ FAILED: ${errorMsg}`);
    console.log(`[ae][verify] Unexpected error: ${errorMsg}`);
  }

  const endTime = new Date();
  const duration = ((endTime.getTime() - startTime.getTime()) / 1000).toFixed(1);

  const summary = success ? '✅ All verification steps passed' : '❌ Some verification steps failed';
  
  // Add failure summary if needed
  const failedSteps = logs.filter(log => log.includes('❌')).length;
  const additionalInfo = failedSteps > 0 ? `\n\n**Failed Steps**: ${failedSteps}` : '';
  
  const report = `# Verification Report

Generated: ${startTime.toISOString()}
Duration: ${duration}s
Mode: ${isStrict ? '🔒 STRICT (CI)' : '🔓 SOFT (Local)'}
Status: ${summary}${additionalInfo}

${logs.join('\n\n')}

---
*Generated by ae-framework verification pipeline*
*AE_TYPES_STRICT=${process.env.AE_TYPES_STRICT || '0'} (strict gates ${isStrict ? 'ENABLED' : 'DISABLED'})*
`;

  try {
    await writeFile('artifacts/verify.md', report);
    console.log(`[ae][verify] Verification report generated -> artifacts/verify.md`);
  } catch (error) {
    console.error(`[ae][verify] Failed to write report: ${error instanceof Error ? error.message : String(error)}`);
  }
  
  console.log(`[ae][verify] Pipeline complete: ${success ? 'PASSED' : 'FAILED'} (${duration}s)`);
  
  if (success) {
    return ok({ logs, duration });
  } else {
    return err({ code: 'E_EXEC', step: 'verify', detail: `${failedSteps} steps failed` });
  }
}