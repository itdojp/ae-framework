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

export default function HealthPage() {
  return (
    <main className="container mx-auto px-4 py-8">
      <div className="max-w-2xl">
        <h1 className="text-2xl font-bold mb-4">Health Status</h1>
        <div className="bg-green-50 border border-green-200 rounded-lg p-4">
          <div className="flex items-center">
            <div className="w-3 h-3 bg-green-500 rounded-full mr-3"></div>
            <span className="text-green-800 font-medium">System Healthy</span>
          </div>
          <p className="text-green-700 mt-2">
            All systems are operational. ae-framework web application is running normally.
          </p>
        </div>
        
        <div className="mt-6 space-y-4">
          <div>
            <h2 className="text-lg font-semibold mb-2">Service Information</h2>
            <ul className="space-y-1 text-gray-600">
              <li><strong>Service:</strong> ae-framework-web</li>
              <li><strong>Version:</strong> 0.1.0</li>
              <li><strong>Environment:</strong> Development</li>
              <li><strong>Framework:</strong> Next.js 14 with App Router</li>
            </ul>
          </div>
          
          <div>
            <h2 className="text-lg font-semibold mb-2">Component Status</h2>
            <ul className="space-y-1 text-gray-600">
              <li><span className="inline-block w-2 h-2 bg-gray-400 rounded-full mr-2"></span>Database: Not configured</li>
              <li><span className="inline-block w-2 h-2 bg-gray-400 rounded-full mr-2"></span>External Services: Not applicable</li>
              <li><span className="inline-block w-2 h-2 bg-green-500 rounded-full mr-2"></span>Memory Usage: OK</li>
            </ul>
          </div>
        </div>
      </div>
    </main>
  );
}