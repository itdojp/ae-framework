<<<<<<< HEAD
// Pre/Post conditions (domain-aware, non-breaking)
// Uses endpoint-specific schemas when shapes are recognizable; otherwise returns true.
=======
// Pre/Post conditions (heuristic, endpoint-agnostic)
// Uses schemas when possible; otherwise returns true (non-blocking skeleton).
>>>>>>> origin/main
import {
  CreateReservationInputSchema,
  InventorySchema,
  ReservationSchema,
  ReservationsIdDeleteInput,
  InventorySkuGetInput,
} from './schemas'

function isObject(v: unknown): v is Record<string, unknown> {
  return !!v && typeof v === 'object' && !Array.isArray(v)
}
<<<<<<< HEAD
=======

export function pre(input: unknown): boolean {
  if (!isObject(input)) return true
  // Try to recognize input shape by keys and validate with schemas
  if ('sku' in input && 'quantity' in input && 'orderId' in input) {
    return CreateReservationInputSchema.safeParse(input).success
  }
  if ('id' in input && Object.keys(input).length === 1) {
    return ReservationsIdDeleteInput.safeParse(input).success
  }
  if ('sku' in input && !('quantity' in input)) {
    return InventorySkuGetInput.safeParse(input).success
  }
// Pre/Post conditions (skeleton)
// Derive from formal properties over time (e.g., no negative stock, idempotency)
>>>>>>> origin/main

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
<<<<<<< HEAD
  // Inventory response should never be negative
  if ('stock' in output && 'sku' in output) {
    const ok = InventorySchema.safeParse(output).success
    if (!ok) return false
    // If input provided sku, ensure it matches
    if (isObject(input) && 'sku' in input) {
      if ((output as any).sku !== (input as any).sku) return false
    }
    return true
  }
  // Reservation response should echo input fields; status must be allowed
  if ('status' in output && 'id' in output && 'sku' in output && 'quantity' in output && 'orderId' in output) {
    const ok = ReservationSchema.safeParse(output).success
    if (!ok) return false
    if (isObject(input) && 'sku' in input && 'quantity' in input && 'orderId' in input) {
      const i = input as any
      const o = output as any
      if (o.sku !== i.sku) return false
      if (o.quantity !== i.quantity) return false
      if (o.orderId !== i.orderId) return false
    }
    return true
  }
=======
  // Validate known domain objects if present
  if ('stock' in output && 'sku' in output) {
    return InventorySchema.safeParse(output).success
  }
  if ('status' in output && 'id' in output && 'sku' in output && 'quantity' in output && 'orderId' in output) {
    return ReservationSchema.safeParse(output).success
  }
  return true
}
>>>>>>> origin/main
  return true
}
