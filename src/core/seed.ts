export function getSeed(): number | undefined {
  const v = process.env['AE_SEED'];
  return v ? Number(v) : undefined;
}
