import { NextResponse } from 'next/server';

export async function GET() {
  const healthCheck = {
    status: 'healthy',
    timestamp: new Date().toISOString(),
    service: 'ae-framework-web',
    version: '0.1.0',
    checks: {
      database: 'not_configured',
      external_services: 'not_applicable',
      memory_usage: 'ok',
    },
  };

  return NextResponse.json(healthCheck);
}