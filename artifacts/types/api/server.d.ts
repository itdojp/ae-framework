import { FastifyInstance } from "fastify";
/**
 * Create and configure Fastify server instance
 */
export declare function createServer(): Promise<FastifyInstance>;
export default function getServer(): Promise<FastifyInstance<import("fastify").RawServerDefault, import("http").IncomingMessage, import("http").ServerResponse<import("http").IncomingMessage>, import("fastify").FastifyBaseLogger, import("fastify").FastifyTypeProviderDefault>>;
