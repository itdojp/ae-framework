#!/usr/bin/env node
import { initTelemetry } from '../infra/telemetry.js';
import { Database, initDatabase } from '../infra/db.js';
import { InventoryServiceImpl } from '../domain/services.js';
import { createServer } from '../api/server.js';
import chalk from 'chalk';
import { reservationRoutes } from '../api/routes/reservations.js';

async function main() {
  // Initialize telemetry
  initTelemetry();

  // Initialize database
  const db = new Database(process.env.DATABASE_URL || 'postgres://app:app@localhost:5432/app');
  await initDatabase(db);

  // Initialize services
  const inventoryService = new InventoryServiceImpl(db);

  // Create app instance
  const app = await createServer();

  // Register routes
  await app.register(reservationRoutes, { inventoryService });

  // Start server
  const port = process.env.PORT ? parseInt(process.env.PORT) : 3000;
  const host = process.env.HOST || '0.0.0.0';

  try {
    await app.listen({ port, host });
    console.log(`Server listening on http://${host}:${port}`);
  } catch (err: unknown) {
    const msg = err instanceof Error ? err.message : String(err);
    app.log.error(chalk.red(`❌ Failed to start server: ${msg}`));
    process.exit(1);
  }
}

main().catch((err: unknown) => {
  const msg = err instanceof Error ? err.message : String(err);
  console.error(chalk.red(`❌ Unhandled server error: ${msg}`));
  process.exit(1);
});
