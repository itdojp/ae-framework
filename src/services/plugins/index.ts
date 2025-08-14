/**
 * MCP Server Plugins Index
 * Export all available plugins for the MCP server
 */

export { RustVerificationPlugin } from './rust-verification-plugin.js';
export type { RustVerificationPluginConfig } from './rust-verification-plugin.js';

// Re-export MCP server types for plugin development
export type {
  MCPPlugin,
  MCPServer,
  MCPEndpoint,
  MCPRequest,
  MCPResponse,
  MCPContext,
  MCPParameter,
  MCPValidationRule
} from '../mcp-server.js';