import { describe, it, expect } from 'vitest'
import { handler as postReservation } from '../../src/routes/reservations-post'
import { handler as deleteReservation } from '../../src/routes/reservations-id-delete'
import { handler as getInventory } from '../../src/routes/inventory-sku-get'

describe('route handlers (contracts-injected skeletons)', () => {
  it('POST /reservations returns 201 with data when input is valid', async () => {
    const res: any = await postReservation({ sku: 'ABC', quantity: 1, orderId: 'O-1' })
    expect(res.status).toBe(201)
  })

  it('DELETE /reservations/:id returns 204', async () => {
    const res: any = await deleteReservation({ id: 'R-1' })
    expect(res.status).toBe(204)
  })

  it('GET /inventory/:sku returns 200 with data', async () => {
    const res: any = await getInventory({ sku: 'ABC' })
    expect(res.status).toBe(200)
  })
})

