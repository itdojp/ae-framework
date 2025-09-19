# Comparator Utility

API for parsing, comparing, and selecting the strictest numeric expressions with unit normalization.

## Exports
- `parseComparator(expr: string): { op: '>=','<=','>','<','==','!=', value: number, unit?: string }`
- `compare(actual: number | string | { value: number; unit?: string }, expr: string): boolean`
- `strictest(a: string, b: string): string`

## Supported Operators
`>=`, `<=`, `>`, `<`, `==`, `!=`

## Units and Normalization
- Percent: `90%` → value `0.9` (ratio), `unit` omitted
- Time: `ms`, `s`, `m`, `h` → normalized to `ms`
  - Examples: `1s` → `1000ms`, `2m` → `120000ms`
- Rate: `rps` (unchanged)

Unknown units are rejected.

## compare() Semantics
- `actual` may be a number, string, or object `{ value, unit? }`.
- If `actual` is unit-less and `expr` specifies a unit, `actual` is interpreted in the unit context of `expr`:
  - Example: `compare(2, '< 3s')` interprets `2` as `2s` (i.e., `2000ms`).
  - For percent expressions, unit-less numbers are treated as ratios (e.g., `0.85`).

## strictest() Rules
- Greater-side (`>`, `>=`): larger thresholds are stricter; at equal threshold, `>` is stricter than `>=`.
- Less-side (`<`, `<=`): smaller thresholds are stricter; at equal threshold, `<` is stricter than `<=`.
- Equality: returned if it lies within the other constraint.
- Mixed directions or combinations that cannot be represented by a single comparator throw.
- Unit differences are normalized before comparison.

## Examples
```ts
parseComparator('>= 90%') // { op: '>=', value: 0.9 }
parseComparator('< 1s')   // { op: '<', value: 1000, unit: 'ms' }
compare('950ms', '< 1s')  // true
strictest('>= 90%', '>= 95%') // '>= 95%'
```

## Error Handling
- Invalid expressions and unsupported units throw `ParseError`.

