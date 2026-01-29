export type ComparatorOperator = '>' | '>=' | '<' | '<=' | '==' | '!=';
export type ComparatorBaseUnit = 'unitless' | 'percent' | 'ms' | 'rps';

export interface ParsedComparator {
  raw: string;
  operator: ComparatorOperator;
  value: number;
  unit: string | null;
  baseUnit: ComparatorBaseUnit;
  normalizedValue: number;
}

const OPERATOR_PATTERN = /^(>=|<=|==|!=|>|<)?\s*([+-]?\d+(?:\.\d+)?)\s*([a-zA-Z%/]+)?$/;
const EPSILON = 1e-9;

const UNIT_ALIASES: Record<string, { baseUnit: ComparatorBaseUnit; factor: number; unit: string } | null> = {
  '%': { baseUnit: 'percent', factor: 1, unit: '%' },
  'percent': { baseUnit: 'percent', factor: 1, unit: '%' },
  'pct': { baseUnit: 'percent', factor: 1, unit: '%' },
  'ms': { baseUnit: 'ms', factor: 1, unit: 'ms' },
  'millisecond': { baseUnit: 'ms', factor: 1, unit: 'ms' },
  'milliseconds': { baseUnit: 'ms', factor: 1, unit: 'ms' },
  's': { baseUnit: 'ms', factor: 1000, unit: 's' },
  'sec': { baseUnit: 'ms', factor: 1000, unit: 's' },
  'secs': { baseUnit: 'ms', factor: 1000, unit: 's' },
  'second': { baseUnit: 'ms', factor: 1000, unit: 's' },
  'seconds': { baseUnit: 'ms', factor: 1000, unit: 's' },
  'm': { baseUnit: 'ms', factor: 60000, unit: 'm' },
  'min': { baseUnit: 'ms', factor: 60000, unit: 'm' },
  'mins': { baseUnit: 'ms', factor: 60000, unit: 'm' },
  'minute': { baseUnit: 'ms', factor: 60000, unit: 'm' },
  'minutes': { baseUnit: 'ms', factor: 60000, unit: 'm' },
  'h': { baseUnit: 'ms', factor: 3600000, unit: 'h' },
  'hr': { baseUnit: 'ms', factor: 3600000, unit: 'h' },
  'hrs': { baseUnit: 'ms', factor: 3600000, unit: 'h' },
  'hour': { baseUnit: 'ms', factor: 3600000, unit: 'h' },
  'hours': { baseUnit: 'ms', factor: 3600000, unit: 'h' },
  'rps': { baseUnit: 'rps', factor: 1, unit: 'rps' },
  'req/s': { baseUnit: 'rps', factor: 1, unit: 'rps' },
  'requests/s': { baseUnit: 'rps', factor: 1, unit: 'rps' },
  'ops/s': { baseUnit: 'rps', factor: 1, unit: 'rps' },
  'rpm': { baseUnit: 'rps', factor: 1 / 60, unit: 'rpm' },
  'req/min': { baseUnit: 'rps', factor: 1 / 60, unit: 'rpm' },
  'requests/min': { baseUnit: 'rps', factor: 1 / 60, unit: 'rpm' },
  'ops/min': { baseUnit: 'rps', factor: 1 / 60, unit: 'rpm' },
};

function normalizeUnit(rawUnit: string | undefined): { baseUnit: ComparatorBaseUnit; normalizedValue: number; unit: string | null } {
  if (!rawUnit) {
    return { baseUnit: 'unitless', normalizedValue: 1, unit: null };
  }

  const key = rawUnit.toLowerCase();
  const info = UNIT_ALIASES[key];
  if (!info) {
    throw new Error(`Unsupported unit: ${rawUnit}`);
  }

  return { baseUnit: info.baseUnit, normalizedValue: info.factor, unit: info.unit };
}

function nearlyEqual(a: number, b: number): boolean {
  const diff = Math.abs(a - b);
  const scale = Math.max(1, Math.abs(a), Math.abs(b));
  return diff <= Math.max(EPSILON, scale * 1e-12);
}

export function parseComparator(expr: string): ParsedComparator {
  const trimmed = expr.trim();
  const match = trimmed.match(OPERATOR_PATTERN);
  if (!match) {
    throw new Error(`Invalid comparator expression: ${expr}`);
  }

  const operator = (match[1] as ComparatorOperator) ?? '>=';
  const numeric = Number.parseFloat(match[2]);
  if (Number.isNaN(numeric)) {
    throw new Error(`Invalid comparator value: ${expr}`);
  }

  const unitInfo = normalizeUnit(match[3]);
  const normalizedValue = numeric * unitInfo.normalizedValue;

  return {
    raw: expr,
    operator,
    value: numeric,
    unit: unitInfo.unit,
    baseUnit: unitInfo.baseUnit,
    normalizedValue,
  };
}

function normalizeActualValue(actual: number | string, comparator: ParsedComparator): number {
  if (typeof actual === 'number') {
    if (comparator.baseUnit === 'percent' && actual <= 1) {
      return actual * 100;
    }
    return actual;
  }

  const trimmed = actual.trim();
  const match = trimmed.match(OPERATOR_PATTERN);
  if (!match) {
    throw new Error(`Invalid actual value: ${actual}`);
  }

  const value = Number.parseFloat(match[2]);
  if (Number.isNaN(value)) {
    throw new Error(`Invalid actual value: ${actual}`);
  }

  const unitInfo = normalizeUnit(match[3]);
  if (unitInfo.baseUnit !== comparator.baseUnit) {
    if (comparator.baseUnit === 'percent' && unitInfo.baseUnit === 'unitless' && value <= 1) {
      return value * 100;
    }
    if (comparator.baseUnit === 'percent' && unitInfo.baseUnit === 'unitless') {
      return value;
    }
    if (comparator.baseUnit === 'unitless' && unitInfo.baseUnit !== 'unitless') {
      throw new Error(`Unit mismatch: expected unitless, got ${match[3] ?? 'unknown'}`);
    }
    throw new Error(`Unit mismatch: expected ${comparator.baseUnit}, got ${unitInfo.baseUnit}`);
  }

  return value * unitInfo.normalizedValue;
}

export function compare(actual: number | string, expr: string): boolean {
  const comparator = parseComparator(expr);
  const actualValue = normalizeActualValue(actual, comparator);
  const expected = comparator.normalizedValue;

  switch (comparator.operator) {
    case '>':
      return actualValue > expected;
    case '>=':
      return actualValue >= expected;
    case '<':
      return actualValue < expected;
    case '<=':
      return actualValue <= expected;
    case '==':
      return nearlyEqual(actualValue, expected);
    case '!=':
      return !nearlyEqual(actualValue, expected);
    default: {
      const exhaustive: never = comparator.operator;
      return exhaustive;
    }
  }
}

function isGreaterOperator(op: ComparatorOperator): boolean {
  return op === '>' || op === '>=';
}

function isLessOperator(op: ComparatorOperator): boolean {
  return op === '<' || op === '<=';
}

function isStrictOperator(op: ComparatorOperator): boolean {
  return op === '>' || op === '<';
}

export function strictest(exprA: string, exprB: string): string {
  const comparatorA = parseComparator(exprA);
  const comparatorB = parseComparator(exprB);

  if (comparatorA.baseUnit !== comparatorB.baseUnit) {
    throw new Error(`Unit mismatch: ${comparatorA.baseUnit} vs ${comparatorB.baseUnit}`);
  }

  if (comparatorA.operator === '==' || comparatorB.operator === '==') {
    const equality = comparatorA.operator === '==' ? comparatorA : comparatorB;
    const other = equality === comparatorA ? comparatorB : comparatorA;
    if (other.operator === '!=') {
      throw new Error('Incompatible comparators: == vs !=');
    }
    if (compare(equality.normalizedValue, other.raw)) {
      return equality.raw;
    }
    throw new Error('Incompatible comparators: equality does not satisfy other comparator');
  }

  if (comparatorA.operator === '!=' || comparatorB.operator === '!=') {
    throw new Error('Incompatible comparators: != is not supported for strictest');
  }

  if (isGreaterOperator(comparatorA.operator) && isGreaterOperator(comparatorB.operator)) {
    if (nearlyEqual(comparatorA.normalizedValue, comparatorB.normalizedValue)) {
      if (isStrictOperator(comparatorA.operator) && !isStrictOperator(comparatorB.operator)) {
        return comparatorA.raw;
      }
      if (isStrictOperator(comparatorB.operator) && !isStrictOperator(comparatorA.operator)) {
        return comparatorB.raw;
      }
      return comparatorA.raw;
    }
    return comparatorA.normalizedValue > comparatorB.normalizedValue ? comparatorA.raw : comparatorB.raw;
  }

  if (isLessOperator(comparatorA.operator) && isLessOperator(comparatorB.operator)) {
    if (nearlyEqual(comparatorA.normalizedValue, comparatorB.normalizedValue)) {
      if (isStrictOperator(comparatorA.operator) && !isStrictOperator(comparatorB.operator)) {
        return comparatorA.raw;
      }
      if (isStrictOperator(comparatorB.operator) && !isStrictOperator(comparatorA.operator)) {
        return comparatorB.raw;
      }
      return comparatorA.raw;
    }
    return comparatorA.normalizedValue < comparatorB.normalizedValue ? comparatorA.raw : comparatorB.raw;
  }

  throw new Error('Incompatible comparators: cannot determine strictest');
}
