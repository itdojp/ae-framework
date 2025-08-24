import fc from 'fast-check';

export function aeAssert<T>(prop: fc.IProperty<T>, opts?: Partial<fc.Parameters<T>>) {
  const seedEnv = process.env.AE_SEED ? Number(process.env.AE_SEED) : undefined;
  return fc.assert(prop, { seed: seedEnv ?? 12345, verbose: true, endOnFailure: true, ...opts });
}