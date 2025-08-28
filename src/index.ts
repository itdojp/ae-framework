// Public library entrypoint (side-effect free)
// Export APIs for consumers without starting any server or processes.
export { createServer } from './api/server.js';
export * as DomainServices from './domain/services.js';
export * as Infra from './infra/db.js';
