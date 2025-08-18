import Fastify, { FastifyInstance } from "fastify";
import { Reservation } from "../domain/contracts.js";
import { securityHeadersPlugin, getSecurityConfiguration } from "./middleware/security-headers.js";

/**
 * Create and configure Fastify server instance
 */
export async function createServer(): Promise<FastifyInstance> {
  const app = Fastify({ logger: true });

  // Register security headers middleware
  await app.register(securityHeadersPlugin, getSecurityConfiguration());

  // Health check endpoint
  app.get("/health", async (req, reply) => {
    return reply.code(200).send({ 
      status: "healthy", 
      timestamp: new Date().toISOString(),
      service: "ae-framework-api"
    });
  });

  // Reservations endpoint
  app.post("/reservations", async (req, reply) => {
    const parsed = Reservation.safeParse(req.body);
    if (!parsed.success) return reply.code(400).send({ error: "INVALID" });
    // const { orderId, itemId, quantity } = parsed.data;
    // TODO: service 層に委譲（在庫確認・冪等処理・トランザクション）
    return reply.code(201).send({ ok: true });
  });

  return app;
}

// Export a configured server instance for backward compatibility
const app = await createServer();
export default app;