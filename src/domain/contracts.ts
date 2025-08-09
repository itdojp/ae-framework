import { z } from "zod";

export const Reservation = z.object({
  orderId: z.string().min(1),
  itemId: z.string().min(1),
  quantity: z.number().int().positive(),
});

export type Reservation = z.infer<typeof Reservation>;