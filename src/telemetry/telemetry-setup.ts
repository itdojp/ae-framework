import { NodeSDK } from '@opentelemetry/sdk-node';
import { Resource } from '@opentelemetry/resources';
import { SemanticResourceAttributes } from '@opentelemetry/semantic-conventions';
import { OTLPTraceExporter } from '@opentelemetry/exporter-trace-otlp-grpc';

// Environment-based configuration
const isProduction = process.env.NODE_ENV === 'production';
const enableOTLP = process.env.OTEL_EXPORTER_OTLP_ENDPOINT !== undefined;

// Configure resource
const resource = new Resource({
  [SemanticResourceAttributes.SERVICE_NAME]: 'ae-framework',
  [SemanticResourceAttributes.SERVICE_VERSION]: '1.0.0',
  [SemanticResourceAttributes.SERVICE_NAMESPACE]: 'phase6',
  [SemanticResourceAttributes.DEPLOYMENT_ENVIRONMENT]: process.env.NODE_ENV || 'development',
});

// Configure exporters
const traceExporter = enableOTLP 
  ? new OTLPTraceExporter({
      url: process.env.OTEL_EXPORTER_OTLP_TRACES_ENDPOINT || process.env.OTEL_EXPORTER_OTLP_ENDPOINT,
    })
  : undefined; // Use default console exporter

// Create SDK instance
export const telemetrySDK = new NodeSDK({
  resource,
  traceExporter,
});

// Initialize telemetry
export function initializeTelemetry(): void {
  try {
    telemetrySDK.start();
    
    if (isProduction || process.env.DEBUG_TELEMETRY) {
      console.log('📊 OpenTelemetry initialized for ae-framework Phase 6');
      console.log(`   Service: ae-framework v1.0.0`);
      console.log(`   Environment: ${process.env.NODE_ENV || 'development'}`);
      console.log(`   OTLP Export: ${enableOTLP ? '✅ Enabled' : '❌ Console only'}`);
    }
  } catch (error) {
    console.error('❌ Failed to initialize OpenTelemetry:', error);
  }
}

// Graceful shutdown
export function shutdownTelemetry(): Promise<void> {
  return telemetrySDK.shutdown();
}

// Process cleanup
process.on('SIGTERM', async () => {
  try {
    await shutdownTelemetry();
    console.log('📊 OpenTelemetry shutdown complete');
  } catch (error) {
    console.error('❌ Error during OpenTelemetry shutdown:', error);
  }
});

// Default initialization (can be disabled via environment variable)
if (process.env.DISABLE_TELEMETRY !== 'true') {
  initializeTelemetry();
}