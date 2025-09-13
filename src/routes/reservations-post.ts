// Route handler implementation for POST /reservations
import { z } from 'zod'
import { ReservationsPostInput, ReservationsPostOutput } from '../contracts/schemas.js'
import { pre, post } from '../contracts/conditions.js'

export async function handler(input: unknown): Promise<unknown> {
  try {
    ReservationsPostInput.parse(input)
    if (!pre(input)) return { status: 400, error: 'Precondition failed' }
    // Minimal compliant output for skeleton
    const i = input as { sku: string; quantity: number; orderId: string }
    const output: unknown = {
      id: 'R-' + Math.random().toString(36).slice(2, 8),
      sku: i.sku,
      quantity: i.quantity,
      orderId: i.orderId,
      status: 'created' as const,
    }
    if (!post(input, output)) return { status: 500, error: 'Postcondition failed' }
    ReservationsPostOutput.parse(output)
    return { status: 201, data: output }
  } catch (e) {
    if (e instanceof z.ZodError) return { status: 400, error: 'Validation error', details: e.errors }
    return { status: 500, error: 'Unhandled error' }
  }
}
