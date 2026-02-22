import { execa, type Options } from 'execa';
import { err, ok, type Result } from './result.js';
import type { AppError } from './errors.js';

type RunOptions = Omit<Options, 'reject'>;

export async function run(step: string, cmd: string, args: string[], opts: RunOptions = {}): Promise<Result<{ stdout: string }, AppError>> {
  try {
    const r = await execa<{ reject: false }>(cmd, args, { reject: false, ...opts });
    if (r.exitCode !== 0) {
      return err({ code: 'E_EXEC', step, detail: `exit ${r.exitCode}` });
    }
    return ok({ stdout: r.stdout ?? '' });
  } catch (e: unknown) {
    return err({ code: 'E_EXEC', step, detail: e instanceof Error ? e.message : String(e) });
  }
}
