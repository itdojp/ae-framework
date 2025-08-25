import { NodeSDK } from '@opentelemetry/sdk-node';
export declare const telemetrySDK: NodeSDK;
export declare function initializeTelemetry(): void;
export declare function shutdownTelemetry(): Promise<void>;
