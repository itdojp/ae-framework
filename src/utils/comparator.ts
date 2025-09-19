export type ComparatorOp = '>=' | '<=' | '>' | '<' | '==' | '!=';

export interface ParsedComparator {
  op: ComparatorOp;
  value: number;
  unit?: string;
}
export type ComparatorExpr = ParsedComparator;

type ValueWithKind = {
  value: number;
  // canonical kinds used internally for comparison
  kind: 'none' | 'ratio' | 'ms' | 'rps';
};

const OP_REGEX = /^\s*(>=|<=|==|!=|>|<)\s*(.+?)\s*$/;

export class ParseError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'ParseError'
  }
}

function normalizeUnit(unit?: string): string | undefined {
  if (!unit) return undefined;
  const u = unit.trim().toLowerCase();
  if (u === '%') return '%';
  if (u === 'ms' || u === 's' || u === 'm' || u === 'h') return u;
  if (u === 'rps') return 'rps';
  return u;
}

function parseNumericWithUnit(input: string): { value: number; unit?: string; kind: ValueWithKind['kind'] } {
  const raw = input.trim();
  // Percentage: e.g., 90%
  if (/^[-+]?\d*\.?\d+\s*%$/.test(raw)) {
    const num = parseFloat(raw.replace('%', '').trim());
    if (!Number.isFinite(num)) throw new ParseError(`Invalid percentage: ${input}`)
    return { value: num / 100, kind: 'ratio' };
  }

  // Generic number with optional unit
  const m = raw.match(/^([-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?)\s*([a-zA-Z%]+)?$/);
  if (!m) {
    throw new ParseError(`Invalid value: ${input}`);
  }
  const val = Number(m[1]);
  const unit = normalizeUnit(m[2]);

  // Time normalization to ms
  if (unit === 'ms' || unit === 's' || unit === 'm' || unit === 'h') {
    let ms = val;
    if (unit === 's') ms = val * 1000;
    else if (unit === 'm') ms = val * 60 * 1000;
    else if (unit === 'h') ms = val * 60 * 60 * 1000;
    return { value: ms, unit: 'ms', kind: 'ms' };
  }

  if (unit === 'rps') {
    return { value: val, unit: 'rps', kind: 'rps' };
  }

  if (unit === '%' || unit === 'percent' || unit === 'pct') {
    return { value: val / 100, kind: 'ratio' };
  }

  // If a unit was provided but not recognized, throw
  if (unit !== undefined) {
    throw new ParseError(`Unsupported unit: ${unit}`);
  }
  // Plain number (unit-less)
  return { value: val, kind: 'none' };
}

function ensureComparableKinds(a: ValueWithKind['kind'], b: ValueWithKind['kind']): boolean {
  if (a === b) return true;
  // Allow ratio vs none (treat numbers as already-ratio if expr expects ratio)
  if ((a === 'ratio' && b === 'none') || (a === 'none' && b === 'ratio')) return true;
  // Allow ms vs none (treat unit-less actual as ms if comparator expects time)
  if ((a === 'ms' && b === 'none') || (a === 'none' && b === 'ms')) return true;
  // Allow rps vs none (treat unit-less actual as rps if comparator expects rps)
  if ((a === 'rps' && b === 'none') || (a === 'none' && b === 'rps')) return true;
  return false;
}

export function parseComparator(expr: string): ParsedComparator {
  const trimmed = String(expr ?? '');
  const m = trimmed.match(OP_REGEX);
  if (!m) throw new ParseError(`Invalid comparator expression: ${expr}`);
  const op = m[1] as ComparatorOp;
  const rest = m[2]!;
  const { value, unit, kind } = parseNumericWithUnit(rest);
  // Percent is normalized to ratio (unit undefined). Time normalized to ms.
  // Return unit only when meaningful (ms or rps)
  if (kind === 'ms') return { op, value, unit: 'ms' };
  if (kind === 'rps') return { op, value, unit: 'rps' };
  return { op, value };
}

function toCanonical(actual: number | string | { value: number; unit?: string }): ValueWithKind {
  if (typeof actual === 'number') {
    return { value: actual, kind: 'none' };
  }
  if (typeof actual === 'string') {
    const { value, kind } = parseNumericWithUnit(actual);
    return { value, kind };
  }
  // object form
  const { value, unit } = actual;
  if (unit) {
    const normalized = parseNumericWithUnit(`${value}${unit}`);
    return { value: normalized.value, kind: normalized.kind };
  }
  return { value, kind: 'none' };
}

function compareNumbers(a: number, b: number, op: ComparatorOp): boolean {
  switch (op) {
    case '>=':
      return a >= b;
    case '>':
      return a > b;
    case '<=':
      return a <= b;
    case '<':
      return a < b;
    case '==':
      return a === b;
    case '!=':
      return a !== b;
  }
}

export type ComparatorValue = { value: number; unit?: string } | number | string

export function compare(actual: ComparatorValue, expr: string): boolean {
  const cmp = parseComparator(expr)
  let act = toCanonical(actual)

  // Determine comparator kind based on normalized unit or % sign presence
  const cmpKind: ValueWithKind['kind'] = cmp.unit === 'ms' ? 'ms' : (cmp.unit === 'rps' ? 'rps' : (/\%/.test(expr) ? 'ratio' : 'none'))

  // If expr has no explicit unit and not a percent, treat both as unit-less numeric
  if (cmpKind === 'none') {
    return compareNumbers(act.value, cmp.value, cmp.op)
  }

  // If actual is unit-less, interpret it in the unit context of expr
  if (act.kind === 'none') {
    if (cmpKind === 'ms') {
      const unitToken = extractExprUnit(expr)
      const scale = unitToken === 's' ? 1000 : unitToken === 'm' ? 60000 : unitToken === 'h' ? 3600000 : 1
      act = { value: act.value * scale, kind: 'ms' }
    } else if (cmpKind === 'ratio') {
      act = { value: act.value, kind: 'ratio' }
    } else if (cmpKind === 'rps') {
      act = { value: act.value, kind: 'rps' }
    }
  }

  if (!ensureComparableKinds(act.kind, cmpKind)) {
    throw new Error(`Incompatible units: actual kind ${act.kind} vs comparator kind ${cmpKind}`)
  }

  return compareNumbers(act.value, cmp.value, cmp.op)
}

export function strictest(a: string, b: string): string {
  const ca = parseComparator(a);
  const cb = parseComparator(b);

  // Preserve ratio classification when unit is undefined to avoid treating
  // unit-less comparators as compatible with time/rps in strictest().
  const kindA: ValueWithKind['kind'] = ca.unit === 'ms' ? 'ms' : (ca.unit === 'rps' ? 'rps' : 'ratio')
  const kindB: ValueWithKind['kind'] = cb.unit === 'ms' ? 'ms' : (cb.unit === 'rps' ? 'rps' : 'ratio')

  if (!ensureComparableKinds(kindA, kindB)) {
    throw new Error('Cannot determine strictest: incompatible units');
  }

  const isGreaterOp = (op: ComparatorOp) => op === '>' || op === '>=';
  const isLessOp = (op: ComparatorOp) => op === '<' || op === '<=';

  // Same direction comparisons
  if (isGreaterOp(ca.op) && isGreaterOp(cb.op)) {
    if (ca.value === cb.value) {
      // At equal threshold, '>' is stricter than '>='
      if (ca.op === '>' && cb.op === '>=') return a;
      if (cb.op === '>' && ca.op === '>=') return b;
      // Same op, equal threshold -> either, return first for stability
      return a;
    }
    return ca.value > cb.value ? a : b;
  }

  if (isLessOp(ca.op) && isLessOp(cb.op)) {
    if (ca.value === cb.value) {
      if (ca.op === '<' && cb.op === '<=') return a;
      if (cb.op === '<' && ca.op === '<=') return b;
      return a;
    }
    return ca.value < cb.value ? a : b;
  }

  // Equality comparisons: if one is equality and the other includes that exact value, equality is stricter
  if (ca.op === '==' && (isGreaterOp(cb.op) || isLessOp(cb.op))) {
    if (compare(ca.value, `${cb.op} ${cb.value}${cb.unit ? cb.unit : ''}`)) return a;
  }
  if (cb.op === '==' && (isGreaterOp(ca.op) || isLessOp(ca.op))) {
    if (compare(cb.value, `${ca.op} ${ca.value}${ca.unit ? ca.unit : ''}`)) return b;
  }

  // Not supported to determine strictest reliably
  throw new Error('Cannot determine strictest for given expressions');
}

function extractExprUnit(expr: string): string | undefined {
  const m = String(expr).match(OP_REGEX)
  if (!m) return undefined
  const rest = m[2]!.trim()
  const um = rest.match(/^[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?\s*([a-zA-Z%]+)?$/)
  return um?.[1]?.toLowerCase()
}
