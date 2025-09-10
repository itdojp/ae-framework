// Route handler implementation for DELETE /reservations/{id}
import { z } from 'zod'
import { InputSchema as reservationsIdDeleteInput, OutputSchema as reservationsIdDeleteOutput } from '../contracts/schemas'
import { pre, post } from '../contracts/conditions'

export async function handler(input: unknown): Promise<unknown> {
  try {
    reservationsIdDeleteInput.parse(input)
    if (!pre(input)) return { status: 400, error: 'Precondition failed' }
    const output: unknown = {}
    if (!post(input, output)) return { status: 500, error: 'Postcondition failed' }
    reservationsIdDeleteOutput.parse(output)
    return { status: 204 }
  } catch (e) {
    if (e instanceof z.ZodError) return { status: 400, error: 'Validation error', details: e.errors }
    return { status: 500, error: 'Unhandled error' }
  }
}

