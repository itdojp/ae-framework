/**
 * API Test Runner
 * Phase 2.3: HTTP API testing with contract validation and performance monitoring
 */
import { TestRunner, TestCase, TestSuite, TestEnvironment, TestResult, TestExecutionSummary, TestCategory } from '../types.js';
export type HttpMethod = 'GET' | 'POST' | 'PUT' | 'PATCH' | 'DELETE' | 'HEAD' | 'OPTIONS';
export interface APITestConfig {
    timeout: number;
    retries: number;
    validateSchema: boolean;
    followRedirects: boolean;
    validateSSL: boolean;
    maxResponseSize: number;
    defaultHeaders: Record<string, string>;
}
export interface HttpRequest {
    method: HttpMethod;
    url: string;
    headers?: Record<string, string>;
    body?: any;
    query?: Record<string, string>;
    auth?: {
        type: 'basic' | 'bearer' | 'apikey' | 'oauth2';
        credentials: Record<string, string>;
    };
    timeout?: number;
    validateStatus?: (status: number) => boolean;
}
export interface HttpResponse {
    status: number;
    statusText: string;
    headers: Record<string, string>;
    body: any;
    size: number;
    time: number;
    redirects: number;
}
export interface APIAssertion {
    type: 'status' | 'header' | 'body' | 'schema' | 'performance' | 'custom';
    field?: string;
    operator: 'equals' | 'contains' | 'matches' | 'gt' | 'lt' | 'gte' | 'lte' | 'exists' | 'not_exists';
    expected: any;
    message?: string;
}
export interface ResponseSchema {
    type: 'json' | 'xml' | 'text' | 'binary';
    schema?: any;
    properties?: Record<string, any>;
    required?: string[];
}
export declare class APITestRunner implements TestRunner {
    readonly id = "api-runner";
    readonly name = "API Test Runner";
    readonly category: TestCategory;
    private config;
    constructor(config: APITestConfig);
    /**
     * Check if runner can execute test
     */
    canRun(test: TestCase): boolean;
    /**
     * Setup API testing environment
     */
    setup(environment: TestEnvironment): Promise<void>;
    /**
     * Teardown API testing environment
     */
    teardown(environment: TestEnvironment): Promise<void>;
    /**
     * Execute single API test
     */
    runTest(test: TestCase, environment: TestEnvironment): Promise<TestResult>;
    /**
     * Execute test suite (delegates to orchestrator)
     */
    runSuite(suite: TestSuite, environment: TestEnvironment): Promise<TestExecutionSummary>;
    /**
     * Execute API test step
     */
    private executeAPIStep;
    /**
     * Execute HTTP request
     */
    private executeRequest;
    /**
     * Execute response validation
     */
    private executeValidation;
    /**
     * Execute data extraction
     */
    private executeExtraction;
    /**
     * Make HTTP request
     */
    private makeRequest;
    /**
     * Generate mock status code
     */
    private getMockStatus;
    /**
     * Generate mock response body
     */
    private getMockResponseBody;
    /**
     * Add authentication to headers
     */
    private addAuthentication;
    /**
     * Validate response against assertion
     */
    private validateAssertion;
    /**
     * Apply comparison operator
     */
    private applyOperator;
    /**
     * Validate response schema
     */
    private validateSchema;
    /**
     * Extract value from object using path
     */
    private extractFromObject;
    /**
     * Parse API action string
     */
    private parseAPIAction;
    /**
     * Check if action is API step
     */
    private isAPIStep;
    /**
     * Before test hook
     */
    beforeTest?(test: TestCase): Promise<void>;
    /**
     * After test hook
     */
    afterTest?(test: TestCase, result: TestResult): Promise<void>;
}
