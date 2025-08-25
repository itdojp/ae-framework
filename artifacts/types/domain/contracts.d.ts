import { z } from "zod";
export declare const Reservation: z.ZodObject<{
    orderId: z.ZodString;
    itemId: z.ZodString;
    quantity: z.ZodNumber;
}, "strip", z.ZodTypeAny, {
    orderId?: string;
    itemId?: string;
    quantity?: number;
}, {
    orderId?: string;
    itemId?: string;
    quantity?: number;
}>;
export type Reservation = z.infer<typeof Reservation>;
