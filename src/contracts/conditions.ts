// Pre/Post conditions (domain-aware, non-breaking)
// Uses endpoint-specific schemas when shapes are recognizable; otherwise returns true.
import {
  CreateReservationInputSchema,
  InventorySchema,
  ReservationSchema,
  ReservationsIdDeleteInput,
  InventorySkuGetInput,
} from './schemas.js'

function isObject(v: unknown): v is Record<string, unknown> {
  return !!v && typeof v === 'object' && !Array.isArray(v)
}

export function pre(input: unknown): boolean {
  if (!isObject(input)) return true
  // Create reservation
  if ('sku' in input && 'quantity' in input && 'orderId' in input) {
    return CreateReservationInputSchema.safeParse(input).success
  }
  // Delete reservation by id
  if ('id' in input && Object.keys(input).length === 1) {
    return ReservationsIdDeleteInput.safeParse(input).success
  }
  // Get inventory by sku
  if ('sku' in input && !('quantity' in input)) {
    return InventorySkuGetInput.safeParse(input).success
  }
  return true
}

export function post(input: unknown, output: unknown): boolean {
  if (!isObject(output)) return true
  // Inventory response should never be negative
  if ('stock' in output && 'sku' in output) {
    const parsedOutput = InventorySchema.safeParse(output)
    if (!parsedOutput.success) return false
    // If input provided sku, ensure it matches
    if (isObject(input) && 'sku' in input) {
      if (typeof input['sku'] !== 'string') return false
      if (parsedOutput.data.sku !== input['sku']) return false
    }
    return true
  }
  // Reservation response should echo input fields; status must be allowed
  if ('status' in output && 'id' in output && 'sku' in output && 'quantity' in output && 'orderId' in output) {
    const parsedOutput = ReservationSchema.safeParse(output)
    if (!parsedOutput.success) return false
    if (isObject(input) && 'sku' in input && 'quantity' in input && 'orderId' in input) {
      const parsedInput = CreateReservationInputSchema.safeParse(input)
      if (!parsedInput.success) return false
      if (parsedOutput.data.sku !== parsedInput.data.sku) return false
      if (parsedOutput.data.quantity !== parsedInput.data.quantity) return false
      if (parsedOutput.data.orderId !== parsedInput.data.orderId) return false
    }
    return true
  }
  return true
}
