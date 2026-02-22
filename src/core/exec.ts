import { execa, type Options } from 'execa';
import { err, ok, type Result } from './result.js';
import type { AppError } from './errors.js';

type RunOptions = Omit<Options, 'reject'>;

export async function run(step: string, cmd: string, args: string[], opts: RunOptions = {}): Promise<Result<{ stdout: string }, AppError>> {
  try {
    const r = await execa(cmd, args, { reject: false, ...opts });
    if (r.exitCode !== 0) {
      return err({ code: 'E_EXEC', step, detail: `exit ${r.exitCode}` });
    }
    const stdout =
      typeof r.stdout === 'string'
        ? r.stdout
        : Array.isArray(r.stdout)
          ? r.stdout.join('\n')
          : r.stdout instanceof Uint8Array
            ? Buffer.from(r.stdout).toString('utf8')
            : '';
    return ok({ stdout });
  } catch (e: unknown) {
    return err({ code: 'E_EXEC', step, detail: e instanceof Error ? e.message : String(e) });
  }
}
