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
  })

  it('GET /inventory/:sku returns 400 on missing sku', async () => {
    const res: any = await getInventory({})
    expect(res.status).toBe(400)
    expect(res.error).toBeDefined()
  })
})

