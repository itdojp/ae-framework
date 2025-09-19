/**
 * Comparator utility for simple numeric constraints.
 *
 * Features:
 * - parse: string | number | Comparator -> Comparator
 * - satisfies: test a numeric value against a comparator
 * - compareStrictness: order comparators by set inclusion (stricter = smaller set)
 * - strictest: pick the strictest comparator from a list when they are compatible
 */

export type ComparatorOp = '>' | '>=' | '<' | '<=' | '=='

export interface Comparator {
  op: ComparatorOp
  target: number
}

/**
 * Parse a comparator from string/number/object.
 * Examples:
 * - '>=80' => { op: '>=', target: 80 }
 * - '< 50' => { op: '<', target: 50 }
 * - '42'   => { op: '>=', target: 42 }  // numeric literal defaults to ">="
 * - 70     => { op: '>=', target: 70 }
 */
export function parseComparator(input: string | number | Comparator): Comparator {
  if (typeof input === 'object' && input && 'op' in input && 'target' in input) {
    const { op, target } = input as Comparator
    validateOp(op)
    if (!isFiniteNumber(target)) throw new Error(`Invalid comparator target: ${target}`)
    return { op, target: Number(target) }
  }

  if (typeof input === 'number') {
    if (!isFiniteNumber(input)) throw new Error(`Invalid comparator target: ${input}`)
    return { op: '>=', target: input }
  }

  if (typeof input !== 'string') {
    throw new Error('Unsupported comparator input')
  }

  const s = input.trim()
  // Try operator + number, allow spaces: '>= 80', '<  5', '==10'
  const m = s.match(/^(>=|<=|>|<|==|=)\s*(-?\d+(?:\.\d+)?)$/)
  if (m) {
    const op = (m[1] === '=' ? '==' : (m[1] as ComparatorOp))
    const num = Number(m[2])
    if (!isFiniteNumber(num)) throw new Error(`Invalid comparator target: ${m[2]}`)
    return { op, target: num }
  }

  // If it's just a number literal string, default to ">="
  const n = Number(s)
  if (isFiniteNumber(n) && String(n) === normalizeNumericLiteral(s)) {
    return { op: '>=', target: n }
  }

  throw new Error(`Unable to parse comparator from: ${input}`)
}

/** Test a value against a comparator */
export function satisfiesComparator(value: number, compLike: string | number | Comparator): boolean {
  if (!isFiniteNumber(value)) return false
  const c = parseComparator(compLike)
  switch (c.op) {
    case '>': return value > c.target
    case '>=': return value >= c.target
    case '<': return value < c.target
    case '<=': return value <= c.target
    case '==': return value === c.target
  }
}

/**
 * Compare strictness of two comparators using set inclusion over reals.
 * Returns:
 *  - 1 if a is stricter than b (S(a) ⊂ S(b))
 *  - -1 if a is looser than b (S(a) ⊃ S(b))
 *  - 0 if equivalent (S(a) = S(b))
 *  - null if incomparable (neither subset nor superset)
 */
export function compareStrictness(aLike: string | number | Comparator, bLike: string | number | Comparator): 1 | -1 | 0 | null {
  const a = parseComparator(aLike)
  const b = parseComparator(bLike)

  const eq = comparatorsEqual(a, b)
  if (eq) return 0

  const aSubsetB = isSubset(a, b)
  const bSubsetA = isSubset(b, a)

  if (aSubsetB && !bSubsetA) return 1
  if (bSubsetA && !aSubsetB) return -1
  return null
}

/**
 * Pick the strictest comparator that implies all others, when representable as a single comparator.
 * - For only lower bounds (>=,>): choose the highest threshold; tie-breaker prefers '>' over '>='
 * - For only upper bounds (<=,<): choose the lowest threshold; tie-breaker prefers '<' over '<='
 * - If any equality (==) exists and it satisfies all comparators: return that equality
 * - Returns null when intersection cannot be represented as a single comparator
 */
export function strictestComparator(list: Array<string | number | Comparator>): Comparator | null {
  const items = list.map(parseComparator)
  if (items.length === 0) return null

  // If there is any equality, ensure all others accept that value
  const eqs = items.filter(i => i.op === '==')
  if (eqs.length > 0) {
    const target = eqs[0]!.target
    const allSame = eqs.every(e => e.target === target)
    if (!allSame) return null
    const ok = items.every(c => satisfiesComparator(target, c))
    return ok ? { op: '==', target } : null
  }

  const lowers = items.filter(i => i.op === '>' || i.op === '>=')
  const uppers = items.filter(i => i.op === '<' || i.op === '<=')

  if (lowers.length > 0 && uppers.length > 0) {
    // Intersection is a range; not representable by a single comparator
    return null
  }

  if (lowers.length === items.length) {
    // pick the highest target; if tie on target, prefer '>'
    const maxTarget = Math.max(...lowers.map(l => l.target))
    const candidates = lowers.filter(l => l.target === maxTarget)
    const op: ComparatorOp = candidates.some(c => c.op === '>') ? '>' : '>='
    return { op, target: maxTarget }
  }

  if (uppers.length === items.length) {
    // pick the lowest target; if tie on target, prefer '<'
    const minTarget = Math.min(...uppers.map(u => u.target))
    const candidates = uppers.filter(u => u.target === minTarget)
    const op: ComparatorOp = candidates.some(c => c.op === '<') ? '<' : '<='
    return { op, target: minTarget }
  }

  return null
}

// ---------- helpers ----------

function validateOp(op: string): asserts op is ComparatorOp {
  if (op !== '>' && op !== '>=' && op !== '<' && op !== '<=' && op !== '==') {
    throw new Error(`Unsupported operator: ${op}`)
  }
}

function isFiniteNumber(n: unknown): n is number {
  return typeof n === 'number' && Number.isFinite(n)
}

function normalizeNumericLiteral(s: string): string {
  // Normalize numeric string to ensure e.g., '42' matches Number('42') -> '42'
  // Keep as-is for integer or decimal representations without extraneous spaces.
  return String(Number(s.trim()))
}

function comparatorsEqual(a: Comparator, b: Comparator): boolean {
  return a.op === b.op && a.target === b.target
}

// Determine if the solution set of `a` is a subset of that of `b` over real numbers.
function isSubset(a: Comparator, b: Comparator): boolean {
  // Use representative checks. For numeric half-lines and points, we can reason analytically.
  if (a.op === '==' && b.op === '==') return a.target === b.target
  if (a.op === '==' && b.op !== '==') return satisfiesComparator(a.target, b)

  // For threshold vs threshold in same direction
  if ((a.op === '>' || a.op === '>=') && (b.op === '>' || b.op === '>=')) {
    // (a) is subset of (b) if it starts at a higher point, or same point and strictness is stronger
    if (a.target > b.target) return true
    if (a.target < b.target) return false
    // same target: '>' is subset of '>='; '>=' is not subset of '>'
    return a.op === '>' && b.op === '>='
  }

  if ((a.op === '<' || a.op === '<=') && (b.op === '<' || b.op === '<=')) {
    // (a) is subset of (b) if it ends at a lower point, or same point and strictness is stronger
    if (a.target < b.target) return true
    if (a.target > b.target) return false
    // same target: '<' is subset of '<='; '<=' is not subset of '<'
    return a.op === '<' && b.op === '<='
  }

  // Opposite directions generally incomparable
  return false
}

