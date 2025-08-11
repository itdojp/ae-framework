import { initTelemetry } from './infra/telemetry.js';
import { Database, initDatabase } from './infra/db.js';
import { InventoryServiceImpl } from './domain/services.js';
import app from './api/server.js';
import { reservationRoutes } from './api/routes/reservations.js';

async function start() {
  // Initialize telemetry
  initTelemetry();

  // Initialize database
  const db = new Database(process.env.DATABASE_URL || 'postgres://app:app@localhost:5432/app');
  await initDatabase(db);

  // Initialize services
  const inventoryService = new InventoryServiceImpl(db);

  // Register routes
  await app.register(reservationRoutes, { inventoryService });

  // Start server
  const port = process.env.PORT ? parseInt(process.env.PORT) : 3000;
  const host = process.env.HOST || '0.0.0.0';

  try {
    await app.listen({ port, host });
    console.log(`Server listening on http://${host}:${port}`);
  } catch (err) {
    app.log.error(err);
    process.exit(1);
  }
}

start().catch(console.error);