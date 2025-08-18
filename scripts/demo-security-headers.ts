#!/usr/bin/env tsx

/**
 * Security Headers Demo Script
 * Demonstrates the security headers implementation
 */

import { createServer } from '../src/api/server.js';
import { getSecurityConfiguration } from '../src/api/middleware/security-headers.js';

async function runDemo() {
  console.log('🔒 AE-Framework Security Headers Demo\n');
  
  // Show configuration
  console.log('📋 Security Configuration (Development):');
  const config = getSecurityConfiguration('development');
  console.log(JSON.stringify(config, null, 2));
  console.log('');
  
  // Create and start server
  console.log('🚀 Starting demo server...');
  const app = await createServer();
  
  try {
    await app.listen({ port: 3000, host: '0.0.0.0' });
    console.log('✅ Demo server running on http://localhost:3000');
    console.log('');
    
    console.log('📋 Available endpoints:');
    console.log('  - GET  http://localhost:3000/health');
    console.log('  - POST http://localhost:3000/reservations');
    console.log('');
    
    console.log('🔍 Test the security headers:');
    console.log('  curl -I http://localhost:3000/health');
    console.log('  pnpm security:check-headers');
    console.log('  pnpm security:scan http://localhost:3000/health');
    console.log('');
    
    console.log('Press Ctrl+C to stop the demo server');
    
    // Keep server running
    process.on('SIGINT', async () => {
      console.log('\n\n🛑 Shutting down demo server...');
      await app.close();
      console.log('✅ Demo complete');
      process.exit(0);
    });
    
  } catch (error) {
    console.error('❌ Error starting demo server:', error);
    process.exit(1);
  }
}

// Run the demo if this script is executed directly
if (import.meta.url === `file://${process.argv[1]}`) {
  runDemo().catch(error => {
    console.error('❌ Demo failed:', error);
    process.exit(1);
  });
}

export { runDemo };