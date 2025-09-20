import { describe, it, expect } from 'vitest'
import { parseComparator, compare } from '../../src/utils/comparator.js'

function bench(fn: () => void, iters = 10000): number {
  const t0 = performance.now()
  for (let i = 0; i < iters; i++) fn()
  const t1 = performance.now()
  return (t1 - t0) / iters
}

describe('perf/comparator', () => {
  it('parses common expressions efficiently (~10k ops)', () => {
    const avgMs = bench(() => {
      parseComparator('>= 90%')
      parseComparator('<= 250ms')
      parseComparator('> 10 rps')
      parseComparator('== 0.75')
    })
    expect(avgMs).toBeLessThan(0.05) // 0.05ms per iteration budget
  })

  it('compares values efficiently (~10k ops)', () => {
    const cmp = parseComparator('<= 1s')
    const avgMs = bench(() => {
      compare('500ms', '<= 1s')
      compare(0.85, '>= 80%')
      compare({ value: 120, unit: 'rps' }, '>= 100 rps')
      void cmp
    })
    expect(avgMs).toBeLessThan(0.05)
  })
})

