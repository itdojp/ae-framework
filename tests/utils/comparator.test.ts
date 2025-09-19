import { describe, it, expect } from 'vitest'
import { parseComparator, satisfiesComparator, compareStrictness, strictestComparator } from '../../src/utils/comparator.js'

describe('Utils: comparator (parse/compare/strictest)', () => {
  describe('parseComparator', () => {
    it('parses basic operators and numbers', () => {
      expect(parseComparator('>=80')).toEqual({ op: '>=', target: 80 })
      expect(parseComparator('> 80')).toEqual({ op: '>', target: 80 })
      expect(parseComparator('<= 50')).toEqual({ op: '<=', target: 50 })
      expect(parseComparator('<5')).toEqual({ op: '<', target: 5 })
      expect(parseComparator('== 42')).toEqual({ op: '==', target: 42 })
      expect(parseComparator('=42')).toEqual({ op: '==', target: 42 })
      expect(parseComparator(70)).toEqual({ op: '>=', target: 70 })
      expect(parseComparator('80')).toEqual({ op: '>=', target: 80 })
    })
  })

  describe('satisfiesComparator', () => {
    it('evaluates numeric values correctly', () => {
      expect(satisfiesComparator(85, '>=80')).toBe(true)
      expect(satisfiesComparator(80, '>80')).toBe(false)
      expect(satisfiesComparator(50, '<=50')).toBe(true)
      expect(satisfiesComparator(49, '<50')).toBe(true)
      expect(satisfiesComparator(50, '<50')).toBe(false)
      expect(satisfiesComparator(42, '==42')).toBe(true)
      expect(satisfiesComparator(41.9, '==42')).toBe(false)
    })
  })

  describe('compareStrictness', () => {
    it('orders lower-bound comparators by threshold and operator', () => {
      expect(compareStrictness('>=70', '>=80')).toBe(-1)
      expect(compareStrictness('>=80', '>=70')).toBe(1)
      expect(compareStrictness('>80', '>=80')).toBe(1)
      expect(compareStrictness('>=80', '>80')).toBe(-1)
      expect(compareStrictness('>=80', '>=80')).toBe(0)
    })

    it('orders upper-bound comparators similarly', () => {
      expect(compareStrictness('<=90', '<=80')).toBe(-1)
      expect(compareStrictness('<80', '<=90')).toBe(1)
      expect(compareStrictness('<=80', '<80')).toBe(-1)
      expect(compareStrictness('<=80', '<=80')).toBe(0)
    })

    it('treats equality as strict if it is a subset of the other', () => {
      expect(compareStrictness('==80', '>=70')).toBe(1)
      expect(compareStrictness('>=70', '==80')).toBe(-1)
    })

    it('returns null for incomparable directions', () => {
      expect(compareStrictness('>=70', '<=80')).toBeNull()
      expect(compareStrictness('<50', '>=40')).toBeNull()
    })
  })

  describe('strictestComparator', () => {
    it('selects the strictest among compatible lower bounds', () => {
      const c = strictestComparator(['>=70', '>=80', '>85'])
      expect(c).toEqual({ op: '>', target: 85 })
    })

    it('selects the strictest among compatible upper bounds', () => {
      const c = strictestComparator(['<=90', '<70'])
      expect(c).toEqual({ op: '<', target: 70 })
    })

    it('prefers equality if it satisfies all others', () => {
      const c = strictestComparator(['>=70', '<=90', '==80'])
      expect(c).toEqual({ op: '==', target: 80 })
    })

    it('returns null for mixed directions without equality', () => {
      expect(strictestComparator(['>=70', '<=90'])).toBeNull()
    })
  })
})

