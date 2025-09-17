import { describe, it, expect } from 'vitest'
import { formatGWT } from '../utils/gwt-format'
import { handler as postReservation } from '../../src/routes/reservations-post'
import { handler as deleteReservation } from '../../src/routes/reservations-id-delete'
import { handler as getInventory } from '../../src/routes/inventory-sku-get'

describe('route handlers (contracts-injected skeletons)', () => {
  it(formatGWT('valid payload', 'POST /reservations', 'returns 201 with data'), async () => {
    const res: any = await postReservation({ sku: 'ABC', quantity: 1, orderId: 'O-1' })
    expect(res.status).toBe(201)
  })

  it(formatGWT('existing id', 'DELETE /reservations/:id', 'returns 204'), async () => {
    const res: any = await deleteReservation({ id: 'R-1' })
    expect(res.status).toBe(204)
    expect(res.data).toBeUndefined()
  })

  it('GET /inventory/:sku returns 200 with data', async () => {
    const res: any = await getInventory({ sku: 'ABC' })
    expect(res.status).toBe(200)
  })
})
