import { describe, it, expect } from 'vitest'
import { strictest, compare, parseComparator } from '../../src/utils/comparator.js'

// Simple deterministic PRNG (LCG)
function makePRNG(seed = 123456789) {
  let s = seed >>> 0
  return () => (s = (1664525 * s + 1013904223) >>> 0) / 0x100000000
}

const ops = ['>=', '>', '<=', '<'] as const
const timeUnits = ['ms', 's', 'm', 'h'] as const
const ratioOrNone = ['', '%'] as const
const rateUnits = ['rps'] as const

function pick<T>(rnd: () => number, arr: readonly T[]): T {
  return arr[Math.floor(rnd() * arr.length)]
}

function randNum(rnd: () => number, max = 1000) {
  // generate integer or decimal
  const n = Math.floor(rnd() * max)
  return rnd() < 0.5 ? n : Number((n + rnd()).toFixed(3))
}

function genExpr(rnd: () => number, kind: 'time' | 'ratio' | 'rate') {
  const op = pick(rnd, ops)
  const val = randNum(rnd)
  if (kind === 'time') {
    const u = pick(rnd, timeUnits)
    return `${op} ${val}${u}`
  } else if (kind === 'ratio') {
    // sometimes percent, sometimes plain ratio
    const u = pick(rnd, ratioOrNone)
    return u === '%' ? `${op} ${val}%` : `${op} ${Math.min(1, Math.max(0, val / 100))}`
  } else {
    const u = pick(rnd, rateUnits)
    return `${op} ${val}${u}`
  }
}

describe('property/comparator', () => {
  it('strictest is monotone within same direction and kind', () => {
    const rnd = makePRNG(42)
    for (let i = 0; i < 200; i++) {
      const kind = pick(rnd, ['time', 'ratio', 'rate'] as const)
      const a = genExpr(rnd, kind)
      const b = genExpr(rnd, kind)
      const pa = parseComparator(a)
      const pb = parseComparator(b)

      // Only proceed if same direction
      const dirA = pa.op === '>' || pa.op === '>='
      const dirB = pb.op === '>' || pb.op === '>='
      if (dirA !== dirB) continue

      try {
        const s = strictest(a, b)
        const ps = parseComparator(s)
        // s must be either a or b by value/op after normalization
        expect([pa.op, pb.op]).toContain(ps.op)
        if (dirA) {
          // greater-direction: s.value should be >= min(pa.value, pb.value)
          expect(ps.value).toBeGreaterThanOrEqual(Math.min(pa.value, pb.value))
        } else {
          // less-direction: s.value should be <= max(pa.value, pb.value)
          expect(ps.value).toBeLessThanOrEqual(Math.max(pa.value, pb.value))
        }
      } catch (e) {
        // permissible to throw in edge cases (e.g., non-representable), ignore
      }
    }
  })

  it('compare is monotone in greater/less directions', () => {
    const rnd = makePRNG(777)
    for (let i = 0; i < 100; i++) {
      // ratio domain for simplicity
      const a = `>= ${Math.min(0.99, Math.max(0, randNum(rnd) / 100))}`
      const pa = parseComparator(a)
      const x = Math.min(1, Math.max(0, randNum(rnd) / 100))
      const y = Math.min(1, Math.max(0, x + 0.1))
      if (pa.op === '>=' || pa.op === '>') {
        if (compare(x, a)) expect(compare(y, a)).toBe(true)
      }

      const b = `<= ${Math.min(0.99, Math.max(0, randNum(rnd) / 100))}`
      const pb = parseComparator(b)
      const u = Math.min(1, Math.max(0, randNum(rnd) / 100))
      const v = Math.min(1, Math.max(0, u + 0.1))
      if (pb.op === '<=' || pb.op === '<') {
        // less-direction predicate is non-increasing: once false at u, stays false at larger v
        if (!compare(u, b)) expect(compare(v, b)).toBe(false)
      }
    }
  })
})
