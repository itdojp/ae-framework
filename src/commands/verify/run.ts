import { writeFile, mkdir, access, constants, readFile } from 'node:fs/promises';
import { exec } from 'node:child_process';
import { promisify } from 'node:util';
import path from 'node:path';
import { run } from '../../core/exec.js';
import { err, ok, isErr, type Result } from '../../core/result.js';
import type { AppError } from '../../core/errors.js';

const execAsync = promisify(exec);

// Environment-based scope controls
const AE_LINT_SCOPE = process.env.AE_LINT_SCOPE || 'src/{providers,commands}/**/*.ts';
const AE_TSC_PROJECT = process.env.AE_TSC_PROJECT || 'tsconfig.verify.json';
const AE_EXPECT_ERROR_STRICT = process.env.AE_EXPECT_ERROR_STRICT !== '0';
const STEP_TIMEOUT_MS = 120000; // 120 seconds per step

interface StepResult {
  name: string;
  status: 'OK' | 'FAIL' | 'TIMEOUT' | 'SKIP';
  duration: number;
  error?: string;
}

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

async function runStepWithTimeout(
  name: string,
  cmd: string,
  args: string[],
  env?: Record<string, string>
): Promise<StepResult> {
  const startTime = Date.now();
  
  try {
    const result = await Promise.race([
      run(name, cmd, args, {
        stdio: 'inherit',
        env: env ? { ...process.env, ...env } : process.env
      }),
      new Promise<never>((_, reject) => 
        setTimeout(() => reject(new Error('TIMEOUT')), STEP_TIMEOUT_MS)
      )
    ]);
    
    const duration = Date.now() - startTime;
    
    if (result.ok) {
      return { name, status: 'OK', duration };
    } else {
      const errorMsg = isErr(result) && 'detail' in result.error 
        ? result.error.detail 
        : isErr(result) ? result.error.code : 'Unknown error';
      return { name, status: 'FAIL', duration, error: errorMsg };
    }
  } catch (error) {
    const duration = Date.now() - startTime;
    
    if (error instanceof Error && error.message === 'TIMEOUT') {
      return { name, status: 'TIMEOUT', duration };
    } else {
      const errorMsg = error instanceof Error ? error.message : String(error);
      return { name, status: 'FAIL', duration, error: errorMsg };
    }
  }
}

export async function verifyRun(): Promise<Result<{ logs: string[]; duration: string }, AppError>> {
  console.log('[ae][verify] Starting staged verification pipeline...');
  await mkdir('artifacts', { recursive: true });
  
  const logs: string[] = [];
  const stepResults: StepResult[] = [];
  const startTime = Date.now();
  const isStrict = process.env.AE_TYPES_STRICT === '1';

  // Define all verification steps
  const steps: Array<{
    name: string;
    check: () => Promise<boolean>;
    execute: () => Promise<StepResult>;
    required: boolean;
  }> = [
    {
      name: 'TypeScript Check',
      check: async () => await hasBin('tsc'),
      execute: async () => {
        if (await hasFile(AE_TSC_PROJECT)) {
          return runStepWithTimeout('TypeScript Check', 'tsc', ['-p', AE_TSC_PROJECT, '--noEmit']);
        } else if (await hasFile('tsconfig.build.json')) {
          return runStepWithTimeout('TypeScript Check', 'tsc', ['-p', 'tsconfig.build.json', '--noEmit']);
        } else {
          return runStepWithTimeout('TypeScript Check', 'tsc', ['--noEmit']);
        }
      },
      required: true
    },
    {
      name: 'ESLint Check',
      check: async () => await hasBin('eslint') && (
        await hasFile('eslint.config.js') || 
        await hasFile('eslint.config.mjs') || 
        await hasFile('eslint.config.ts')
      ),
      execute: async () => runStepWithTimeout('ESLint Check', 'eslint', [AE_LINT_SCOPE]),
      required: true
    },
    {
      name: 'TSD Type Tests',
      check: async () => await hasScript('test:types'),
      execute: async () => runStepWithTimeout('TSD Type Tests', 'pnpm', ['run', 'test:types']),
      required: false
    },
    {
      name: 'API Snapshot Check',
      check: async () => await hasScript('api:check'),
      execute: async () => runStepWithTimeout('API Snapshot Check', 'pnpm', ['run', 'api:check']),
      required: false
    },
    {
      name: 'API Report Generation',
      check: async () => await hasScript('api:report'),
      execute: async () => {
        // Run api:emit first, then api:report
        const emitResult = await runStepWithTimeout('API Emit', 'pnpm', ['run', 'api:emit']);
        if (emitResult.status !== 'OK') return emitResult;
        return runStepWithTimeout('API Report Generation', 'pnpm', ['run', 'api:report']);
      },
      required: false
    },
    {
      name: 'API Breaking Changes',
      check: async () => await hasScript('api:diff'),
      execute: async () => runStepWithTimeout('API Breaking Changes', 'pnpm', ['run', 'api:diff']),
      required: false
    },
    {
      name: '@ts-expect-error Policy',
      check: async () => AE_EXPECT_ERROR_STRICT && await hasFile('scripts/ci/check-expect-error.mjs'),
      execute: async () => runStepWithTimeout('@ts-expect-error Policy', 'node', ['scripts/ci/check-expect-error.mjs']),
      required: true
    }
  ];

  // Execute all steps regardless of failures
  for (const stepDef of steps) {
    const canRun = await stepDef.check();
    
    if (!canRun) {
      const result: StepResult = { name: stepDef.name, status: 'SKIP', duration: 0 };
      stepResults.push(result);
      console.log(`[ae][verify] step=${stepDef.name} status=SKIP dur=0ms (requirements not met)`);
      logs.push(`## ${stepDef.name}\nℹ️ SKIPPED (requirements not met)`);
      continue;
    }

    console.log(`[ae][verify] step=${stepDef.name} status=RUNNING`);
    
    try {
      const result = await stepDef.execute();
      stepResults.push(result);
      
      const statusIcon = result.status === 'OK' ? '✅' : 
                        result.status === 'TIMEOUT' ? '⏱️' :
                        result.status === 'FAIL' ? '❌' : '⚠️';
      
      console.log(`[ae][verify] step=${result.name} status=${result.status} dur=${result.duration}ms`);
      
      if (result.status === 'OK') {
        logs.push(`## ${result.name}\n${statusIcon} PASSED (${result.duration}ms)`);
      } else if (result.status === 'TIMEOUT') {
        logs.push(`## ${result.name}\n${statusIcon} TIMEOUT after ${STEP_TIMEOUT_MS/1000}s`);
      } else {
        const errorInfo = result.error ? ` (${result.error})` : '';
        logs.push(`## ${result.name}\n${statusIcon} FAILED${errorInfo} (${result.duration}ms)`);
      }
    } catch (error) {
      const result: StepResult = { 
        name: stepDef.name, 
        status: 'FAIL', 
        duration: 0, 
        error: error instanceof Error ? error.message : String(error)
      };
      stepResults.push(result);
      
      console.log(`[ae][verify] step=${stepDef.name} status=FAIL dur=0ms (execution error)`);
      logs.push(`## ${stepDef.name}\n❌ EXECUTION ERROR (${result.error})`);
    }
  }

  // Calculate final results
  const totalDuration = Date.now() - startTime;
  const failed = stepResults.filter(r => r.status === 'FAIL' || r.status === 'TIMEOUT');
  const passed = stepResults.filter(r => r.status === 'OK');
  const skipped = stepResults.filter(r => r.status === 'SKIP');
  
  const hasFailures = failed.length > 0;
  const shouldFail = isStrict && hasFailures;

  // Generate comprehensive summary
  const modeStr = isStrict ? '🔒 STRICT (CI)' : '🔓 SOFT (Local)';
  const statusStr = shouldFail ? '❌ FAILED' : hasFailures ? '⚠️ PARTIAL' : '✅ PASSED';
  
  const summary = `# Staged Verification Report

Generated: ${new Date(startTime).toISOString()}
Duration: ${(totalDuration / 1000).toFixed(1)}s
Mode: ${modeStr}
Status: ${statusStr}

## Summary Statistics
- ✅ Passed: ${passed.length}
- ❌ Failed: ${failed.length} 
- ⏱️ Timeouts: ${stepResults.filter(r => r.status === 'TIMEOUT').length}
- ⚠️ Skipped: ${skipped.length}

## Environment Controls
- AE_TYPES_STRICT: ${process.env.AE_TYPES_STRICT || '0'} (${isStrict ? 'ENABLED' : 'DISABLED'})
- AE_LINT_SCOPE: ${AE_LINT_SCOPE}
- AE_TSC_PROJECT: ${AE_TSC_PROJECT}
- AE_EXPECT_ERROR_STRICT: ${AE_EXPECT_ERROR_STRICT ? '1' : '0'}
- STEP_TIMEOUT: ${STEP_TIMEOUT_MS/1000}s

## Step Results

${logs.join('\n\n')}

---
*Generated by ae-framework staged verification pipeline*
*Exit behavior: ${isStrict ? 'failures cause exit 1' : 'warnings only (exit 0)'}*
`;

  try {
    await writeFile('artifacts/verify.md', summary);
    console.log(`[ae][verify] Report generated -> artifacts/verify.md`);
  } catch (error) {
    console.error(`[ae][verify] Failed to write report: ${error instanceof Error ? error.message : String(error)}`);
  }
  
  console.log(`[ae][verify] Pipeline complete: ${statusStr} (${(totalDuration/1000).toFixed(1)}s)`);
  console.log(`[ae][verify] Results: ${passed.length} passed, ${failed.length} failed, ${skipped.length} skipped`);
  
  if (shouldFail) {
    return err({ code: 'E_EXEC', step: 'verify', detail: `${failed.length} steps failed in strict mode` });
  } else {
    return ok({ logs: [summary], duration: `${(totalDuration/1000).toFixed(1)}s` });
  }
}