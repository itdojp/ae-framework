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
      expect(typeof res.data).toBe('object')
      expect('title' in res.data || 'detail' in res.data).toBe(true)
<<<<<<< HEAD
      if ('status' in res.data) expect(typeof res.data.status).toBe('number')
      if ('title' in res.data) expect(typeof res.data.title).toBe('string')
=======
>>>>>>> origin/main
    }
  })

  it('GET /inventory/:sku returns 400 on missing sku', async () => {
    const res: any = await getInventory({})
    expect(res.status).toBe(400)
    expect(res.error).toBeDefined()
  })
})
