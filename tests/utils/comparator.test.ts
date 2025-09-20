import { describe, it, expect } from 'vitest'
import { parseComparator, compare, strictest } from '../../src/utils/comparator.js'

describe('utils/comparator', () => {
  describe('parseComparator', () => {
    it('parses percentage and normalizes to ratio', () => {
      const c = parseComparator('>= 90%')
      expect(c).toEqual({ op: '>=', value: 0.9, unit: undefined })
    })

    it('parses time and normalizes to ms', () => {
      const gt = parseComparator('>1s')
      expect(gt).toEqual({ op: '>', value: 1000, unit: 'ms' })

      const le = parseComparator('<= 500ms')
      expect(le).toEqual({ op: '<=', value: 500, unit: 'ms' })
    })

    it('parses rps unit', () => {
      const eq = parseComparator('== 200 rps')
      expect(eq).toEqual({ op: '==', value: 200, unit: 'rps' })
    })

    it('rejects invalid expressions/units', () => {
      expect(() => parseComparator('>>10')).toThrow()
      expect(() => parseComparator('>=10kb')).toThrow()
    })

    it('tolerates extra spaces and uppercase units', () => {
      expect(parseComparator('  <=   2S  ')).toEqual({ op: '<=', value: 2000, unit: 'ms' })
      expect(parseComparator('>   1e3 ms')).toEqual({ op: '>', value: 1000, unit: 'ms' })
    })
  })

  describe('compare', () => {
    it('compares ratio against percentage expression', () => {
      expect(compare(0.95, '>= 90%')).toBe(true)
      expect(compare(0.89, '>= 90%')).toBe(false)
    })

    it('compares percentage actual string against numeric expression', () => {
      expect(compare('95%', '>= 0.9')).toBe(true)
      expect(compare('80%', '>= 0.9')).toBe(false)
    })

    it('compares time across mixed units', () => {
      expect(compare('950ms', '< 1s')).toBe(true)
      expect(compare({ value: 1, unit: 's' }, '<= 1000ms')).toBe(true)
      expect(compare({ value: 2, unit: 's' }, '<= 1500ms')).toBe(false)
    })

    it('interprets unit-less actual in expr unit context', () => {
      // expr uses seconds; actual unit-less 1 -> 1s -> 1000ms
      expect(compare(1, '< 2s')).toBe(true)
      // expr uses ms; actual 1 -> 1ms
      expect(compare(1, '>= 1ms')).toBe(true)
    })

    it('compares rps unit', () => {
      expect(compare({ value: 120, unit: 'rps' }, '>= 100 rps')).toBe(true)
      expect(compare(80, '>= 100 rps')).toBe(false)
    })

    it('supports equality and inequality', () => {
      expect(compare('85%', '== 0.85')).toBe(true)
      expect(compare(5, '!= 5')).toBe(false)
      expect(compare(5, '!= 6')).toBe(true)
    })

    it('throws on invalid actual inputs', () => {
      expect(() => compare('10kb', '>= 1s')).toThrow()
    })
  })

  describe('strictest', () => {
    it('returns stricter for greater-direction comparators', () => {
      expect(strictest('>= 90%', '>= 95%')).toBe('>= 95%')
      expect(strictest('> 10 rps', '>= 10 rps')).toBe('> 10 rps')
    })

    it('returns stricter for less-direction comparators', () => {
      expect(strictest('< 500ms', '<= 1s')).toBe('< 500ms')
      expect(strictest('<= 400ms', '<= 1s')).toBe('<= 400ms')
    })

    it('prefers equality when inside bounds', () => {
      expect(strictest('>= 0.7', '== 0.8')).toBe('== 0.8')
    })

    it('throws for mixed directions or unsupported', () => {
      expect(() => strictest('>= 0.7', '<= 0.9')).toThrow()
    })

    it('throws on incomparable kinds (ratio vs time)', () => {
      expect(() => strictest('>= 0.5', '>= 100ms')).toThrow()
    })

    it('regression: representative expressions from fixtures', async () => {
      const fs = await import('fs/promises')
      const path = await import('path')
      const p = path.join(process.cwd(), 'tests/fixtures/comparator-exprs.txt')
      const lines = (await fs.readFile(p, 'utf-8')).split(/\r?\n/).filter(Boolean)
      // ensure all lines parse
      for (const line of lines) {
        expect(() => parseComparator(line)).not.toThrow()
      }
    })
  })
})
