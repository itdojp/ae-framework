import { describe, it, expect } from 'vitest'
import { handler as postReservation } from '../../src/routes/reservations-post'
import { handler as getInventory } from '../../src/routes/inventory-sku-get'

describe('route handlers (error paths)', () => {
  it('POST /reservations returns 400 on validation error', async () => {
    const res: any = await postReservation({})
    expect(res.status).toBe(400)
    expect(res.error).toBeDefined()
    // zod error details should be present
    expect(res.details).toBeDefined()
    // minimal RFC7807-like body when problem+json is defined
    if (res.data) {
      const d: any = res.data
      expect(typeof d).toBe('object')
      expect('title' in d || 'detail' in d).toBe(true)
      if ('status' in d) expect(typeof d.status).toBe('number')
      if ('title' in d) expect(typeof d.title).toBe('string')
    }
  })

  it('GET /inventory/:sku returns 400 on missing sku', async () => {
    const res: any = await getInventory({})
    expect(res.status).toBe(400)
    expect(res.error).toBeDefined()
  })
})
