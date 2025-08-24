import fc from 'fast-check';

export const arbEmail = fc.oneof(
  fc.emailAddress(), // 正例
  fc.string()        // ノイズ（負例）
);

export function multiset<T>(arr: T[]) {
  const m = new Map<T, number>();
  for (const x of arr) m.set(x, (m.get(x) ?? 0) + 1);
  return m;
}

export function expectMultisetEqual<T>(a: T[], b: T[]) {
  const ma = multiset(a), mb = multiset(b);
  if (ma.size !== mb.size) throw new Error('multiset size differs');
  for (const [k,v] of ma) if (mb.get(k) !== v) throw new Error(`count differs for ${String(k)}`);
}