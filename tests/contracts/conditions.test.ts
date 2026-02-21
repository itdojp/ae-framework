import { describe, expect, it } from 'vitest'
import { post } from '../../src/contracts/conditions.js'

describe('contracts/conditions post', () => {
  it('returns true when inventory output sku matches input sku', () => {
    const input = { sku: 'sku-1' }
    const output = { sku: 'sku-1', stock: 10 }
    expect(post(input, output)).toBe(true)
  })

  it('returns false when inventory output sku does not match input sku', () => {
    const input = { sku: 'sku-1' }
    const output = { sku: 'sku-2', stock: 10 }
    expect(post(input, output)).toBe(false)
  })

  it('returns false when inventory input sku is not a string', () => {
    const input = { sku: 123 }
    const output = { sku: 'sku-1', stock: 10 }
    expect(post(input, output)).toBe(false)
  })

  it('returns false when inventory output has negative stock', () => {
    const input = { sku: 'sku-1' }
    const output = { sku: 'sku-1', stock: -5 }
    expect(post(input, output)).toBe(false)
  })

  it('returns true when reservation output echoes input fields', () => {
    const input = { sku: 'sku-1', quantity: 2, orderId: 'order-1' }
    const output = {
      id: 'res-1',
      sku: 'sku-1',
      quantity: 2,
      orderId: 'order-1',
      status: 'created',
    }
    expect(post(input, output)).toBe(true)
  })

  it('returns false when reservation output does not echo input fields', () => {
    const input = { sku: 'sku-1', quantity: 2, orderId: 'order-1' }
    const output = {
      id: 'res-1',
      sku: 'sku-1',
      quantity: 2,
      orderId: 'order-2',
      status: 'created',
    }
    expect(post(input, output)).toBe(false)
  })

  it('returns false when reservation output has an invalid status', () => {
    const input = { sku: 'sku-1', quantity: 2, orderId: 'order-1' }
    const output = {
      id: 'res-1',
      sku: 'sku-1',
      quantity: 2,
      orderId: 'order-1',
      status: 'invalid-status',
    }
    expect(post(input, output)).toBe(false)
  })

  it('returns true when input/output do not match recognized patterns', () => {
    const input = { foo: 'bar' }
    const output = { baz: 'qux' }
    expect(post(input, output)).toBe(true)
  })
})
