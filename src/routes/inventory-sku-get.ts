// Route handler implementation for GET /inventory/{sku}
import { z } from 'zod'
import { InventorySkuGetInput, InventorySkuGetOutput } from '../contracts/schemas.js'
import { pre, post } from '../contracts/conditions.js'

export async function handler(input: unknown): Promise<unknown> {
  try {
    InventorySkuGetInput.parse(input)
    if (!pre(input)) return { status: 400, error: 'Precondition failed' }
    const i = input as { sku: string }
    const output: unknown = { sku: i.sku, stock: 0 }
    if (!post(input, output)) return { status: 500, error: 'Postcondition failed' }
    InventorySkuGetOutput.parse(output)
    return { status: 200, data: output }
  } catch (e) {
    if (e instanceof z.ZodError) return { status: 400, error: 'Validation error', details: e.errors }
    return { status: 500, error: 'Unhandled error' }
  }
}
