import fc from 'fast-check';
import { writeRepro } from '../../tests/_failures/repro-writer.js';

export function aeAssert<T>(prop: fc.IProperty<T>, opts?: Partial<fc.Parameters<T>>) {
  const seedEnv = process.env['AE_SEED'] ? Number(process.env['AE_SEED']) : undefined;
  return fc.assert(prop, { seed: seedEnv ?? 12345, verbose: true, endOnFailure: true, ...opts });
}

export function aeAssertRepro<T>(name: string, prop: fc.IProperty<T>, opts?: Partial<fc.Parameters<T>>) {
  const seed = process.env['AE_SEED'] ? Number(process.env['AE_SEED']) : 12345;
  try {
    fc.assert(prop, { seed, verbose: true, endOnFailure: true, ...opts });
  } catch (e: any) {
    // Extract counterexample from fast-check error message
    // Fast-check puts the counterexample in the error message
    let shrunk = null;
    if (e?.message && typeof e.message === 'string') {
      // Try to extract from "Encountered failures were:" section
      const failuresMatch = e.message.match(/Encountered failures were:\s*\n- (.+)$/);
      if (failuresMatch && failuresMatch[1]) {
        try {
          shrunk = JSON.parse(failuresMatch[1]);
        } catch {
          shrunk = failuresMatch[1]; // fallback to raw string
        }
      }
    }
    
    // Fallback extraction attempts
    shrunk = shrunk ?? e?.counterexample ?? e?.shrunk ?? e?.value ?? null;
    
    writeRepro(name, seed, shrunk).catch(() => {}); // Silent failure for repro writing
    throw e;
  }
}
