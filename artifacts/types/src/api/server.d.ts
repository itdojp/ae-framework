import Fastify, { FastifyInstance } from "fastify";
/**
 * Create and configure Fastify server instance
 */
export declare function createServer(): Promise<FastifyInstance>;
export default function getServer(): Promise<Fastify.FastifyInstance<Fastify.RawServerDefault, import("http").IncomingMessage, import("http").ServerResponse<import("http").IncomingMessage>, Fastify.FastifyBaseLogger, Fastify.FastifyTypeProviderDefault>>;
