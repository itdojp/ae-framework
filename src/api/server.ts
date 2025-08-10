import Fastify from "fastify";
import { Reservation } from "../domain/contracts.js";

const app = Fastify({ logger: true });

app.post("/reservations", async (req, reply) => {
  const parsed = Reservation.safeParse(req.body);
  if (!parsed.success) return reply.code(400).send({ error: "INVALID" });
  const { orderId, itemId, quantity } = parsed.data;
  // TODO: service 層に委譲（在庫確認・冪等処理・トランザクション）
  return reply.code(201).send({ ok: true });
});

export default app;