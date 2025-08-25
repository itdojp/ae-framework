import { execa } from 'execa';
import { writeFile, mkdir, access, constants } from 'node:fs/promises';
import { exec } from 'node:child_process';
import { promisify } from 'node:util';
import path from 'node:path';

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

export async function verifyRun() {
  console.log('[ae][verify] Starting verification pipeline...');
  await mkdir('artifacts', { recursive: true });
  
  const logs: string[] = [];
  let ok = true;
  const startTime = new Date();

  async function step(name: string, cmd: string, args: string[], env?: Record<string, string>) {
    logs.push(`## ${name}\n\`\`\`bash\n${[cmd, ...args].join(' ')}\n\`\`\``);
    console.log(`[ae][verify] ${name} start`);
    
    try {
      const r = await execa(cmd, args, { 
        reject: false, 
        stdio: 'inherit', 
        env: env ? { ...process.env, ...env } : process.env 
      });
      
      if (r.exitCode !== 0) { 
        ok = false; 
        logs.push(`❌ ${name}: FAILED (exit ${r.exitCode})`);
        console.log(`[ae][verify] ${name} end: FAILED`);
      } else { 
        logs.push(`✅ ${name}: OK`);
        console.log(`[ae][verify] ${name} end: OK`);
      }
    } catch (error) {
      ok = false;
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`❌ ${name}: FAILED (error: ${errorMsg})`);
      console.log(`[ae][verify] ${name} end: FAILED (error: ${errorMsg})`);
    }
  }

  try {
    // 1) TypeScript type check (prioritize scoped config)
    try {
      if (await hasBin('tsc')) {
        if (await hasFile('tsconfig.verify.json')) {
          await step('TypeScript Types', 'tsc', ['-p', 'tsconfig.verify.json']);
        } else if (await hasFile('tsconfig.build.json')) {
          await step('TypeScript Types', 'tsc', ['-p', 'tsconfig.build.json']);
        } else {
          await step('TypeScript Types', 'tsc', ['--noEmit']);
        }
      } else {
        logs.push('## TypeScript Types\nℹ️  Skipped (tsc not available)');
        console.log('[ae][verify] TypeScript Types: SKIPPED (tsc not available)');
      }
    } catch (error) {
      ok = false;
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## TypeScript Types\n❌ FAILED (error: ${errorMsg})`);
      console.log(`[ae][verify] TypeScript Types: FAILED (error: ${errorMsg})`);
    }

    // 2) ESLint (check for flat config, graceful skip if missing)
    try {
      if (await hasBin('eslint')) {
        if (await hasFile('eslint.config.js') || await hasFile('eslint.config.mjs') || await hasFile('eslint.config.ts')) {
          await step('ESLint', 'eslint', ['.']);
        } else {
          logs.push('## ESLint\n⚠️  WARN: No flat config (eslint.config.js) found - skipped');
          console.log('[ae][verify] ESLint: WARN (no flat config found, skipped)');
        }
      } else {
        logs.push('## ESLint\nℹ️  Skipped (eslint not available)');
        console.log('[ae][verify] ESLint: SKIPPED (eslint not available)');
      }
    } catch (error) {
      ok = false;
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
      ok = false;
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
      ok = false;
      const errorMsg = error instanceof Error ? error.message : String(error);
      logs.push(`## Benchmarks\n❌ FAILED (error: ${errorMsg})`);
      console.log(`[ae][verify] Benchmarks: FAILED (error: ${errorMsg})`);
    }

  } catch (unexpectedError) {
    ok = false;
    const errorMsg = unexpectedError instanceof Error ? unexpectedError.message : String(unexpectedError);
    logs.push(`## Unexpected Error\n❌ FAILED: ${errorMsg}`);
    console.log(`[ae][verify] Unexpected error: ${errorMsg}`);
  } finally {
    const endTime = new Date();
    const duration = ((endTime.getTime() - startTime.getTime()) / 1000).toFixed(1);

    const summary = ok ? '✅ All verification steps passed' : '❌ Some verification steps failed';
    
    // Add failure summary if needed
    const failedSteps = logs.filter(log => log.includes('❌')).length;
    const additionalInfo = failedSteps > 0 ? `\n\n**Failed Steps**: ${failedSteps}` : '';
    
    const report = `# Verification Report

Generated: ${startTime.toISOString()}
Duration: ${duration}s
Status: ${summary}${additionalInfo}

${logs.join('\n\n')}

---
*Generated by ae-framework verification pipeline*
`;

    try {
      await writeFile('artifacts/verify.md', report);
      console.log(`[ae][verify] Verification report generated -> artifacts/verify.md`);
    } catch (error) {
      console.error(`[ae][verify] Failed to write report: ${error instanceof Error ? error.message : String(error)}`);
    }
    
    console.log(`[ae][verify] Pipeline complete: ${ok ? 'PASSED' : 'FAILED'} (${duration}s)`);
  }
  
  process.exit(ok ? 0 : 1);
}