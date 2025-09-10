// Route handler implementation for POST /reservations
import { z } from 'zod'
import { ReservationsPostInput, ReservationsPostOutput } from '../contracts/schemas'
import { pre, post } from '../contracts/conditions'

export async function handler(input: unknown): Promise<unknown> {
  try {
    ReservationsPostInput.parse(input)
    if (!pre(input)) return { status: 400, error: 'Precondition failed' }
    // TODO: actual implementation here
    const output: unknown = {}
    if (!post(input, output)) return { status: 500, error: 'Postcondition failed' }
    ReservationsPostOutput.parse(output)
    return { status: 201, data: output }
  } catch (e) {
    if (e instanceof z.ZodError) return { status: 400, error: 'Validation error', details: e.errors }
    return { status: 500, error: 'Unhandled error' }
  }
}
