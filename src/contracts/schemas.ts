import { z } from 'zod'

// Generic fallbacks (kept for compatibility)
export const InputSchema = z.any()
export const OutputSchema = z.any()

// Domain-specific schemas derived from artifacts/codex/openapi.yaml
export const CreateReservationInputSchema = z.object({
  sku: z.string(),
  quantity: z.number().int().min(1),
  orderId: z.string(),
})

export const ReservationSchema = z.object({
  id: z.string(),
  sku: z.string(),
  quantity: z.number().int().min(1),
  orderId: z.string(),
  status: z.enum(['created', 'canceled']),
})

export const InventorySchema = z.object({
  sku: z.string(),
  stock: z.number().int().min(0),
})

// Endpoint-specific aliases
export const ReservationsPostInput = CreateReservationInputSchema
export const ReservationsPostOutput = ReservationSchema

export const ReservationsIdDeleteInput = z.object({ id: z.string() })
export const ReservationsIdDeleteOutput = z.object({}).optional()

export const InventorySkuGetInput = z.object({ sku: z.string() })
export const InventorySkuGetOutput = InventorySchema
// Minimal skeleton schemas; refine per domain as needed
export const InputSchema = z.any()
export const OutputSchema = z.any()

