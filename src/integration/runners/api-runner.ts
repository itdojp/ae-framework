/**
 * API Test Runner
 * Phase 2.3: HTTP API testing with contract validation and performance monitoring
 */

import { v4 as uuidv4 } from 'uuid';
import {
  TestRunner,
  TestCase,
  TestSuite,
  TestEnvironment,
  TestResult,
  TestExecutionSummary,
  TestCategory,
  PerformanceMetrics
} from '../types.js';

// HTTP methods
export type HttpMethod = 'GET' | 'POST' | 'PUT' | 'PATCH' | 'DELETE' | 'HEAD' | 'OPTIONS';

// API test configuration
export interface APITestConfig {
  timeout: number;
  retries: number;
  validateSchema: boolean;
  followRedirects: boolean;
  validateSSL: boolean;
  maxResponseSize: number; // bytes
  defaultHeaders: Record<string, string>;
}

// HTTP request definition
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

// HTTP response
export interface HttpResponse {
  status: number;
  statusText: string;
  headers: Record<string, string>;
  body: any;
  size: number;
  time: number; // response time in ms
  redirects: number;
}

// API assertion types
export interface APIAssertion {
  type: 'status' | 'header' | 'body' | 'schema' | 'performance' | 'custom';
  field?: string;
  operator: 'equals' | 'contains' | 'matches' | 'gt' | 'lt' | 'gte' | 'lte' | 'exists' | 'not_exists';
  expected: any;
  message?: string;
}

// Schema validation
export interface ResponseSchema {
  type: 'json' | 'xml' | 'text' | 'binary';
  schema?: any; // JSON Schema or other schema definition
  properties?: Record<string, any>;
  required?: string[];
}

export class APITestRunner implements TestRunner {
  readonly id = 'api-runner';
  readonly name = 'API Test Runner';
  readonly category: TestCategory = 'integration';

  private config: APITestConfig;

  constructor(config: APITestConfig) {
    this.config = config;
  }

  /**
   * Check if runner can execute test
   */
  canRun(test: TestCase): boolean {
    return (test.category === 'integration' || test.category === 'contract') && 
           test.steps.some(step => this.isAPIStep(step.action));
  }

  /**
   * Setup API testing environment
   */
  async setup(environment: TestEnvironment): Promise<void> {
    // Validate API endpoint connectivity
    if (environment.apiUrl) {
      try {
        const response = await this.makeRequest({
          method: 'GET',
          url: `${environment.apiUrl}/health`,
          timeout: this.config.timeout
        });
        
        if (response.status >= 400) {
          console.warn(`API health check returned status ${response.status}`);
        }
      } catch (error) {
        console.warn('API health check failed:', error);
      }
    }
  }

  /**
   * Teardown API testing environment
   */
  async teardown(environment: TestEnvironment): Promise<void> {
    // Cleanup resources if needed
  }

  /**
   * Execute single API test
   */
  async runTest(test: TestCase, environment: TestEnvironment): Promise<TestResult> {
    const startTime = new Date().toISOString();
    const resultId = uuidv4();
    
    try {
      const stepResults = [];
      const logs: string[] = [];
      const metrics = {
        networkCalls: 0,
        databaseQueries: 0
      };

      // Execute test steps
      for (const step of test.steps) {
        const stepStartTime = new Date().toISOString();
        
        try {
          const actualResult = await this.executeAPIStep(step, environment);
          
          const stepEndTime = new Date().toISOString();
          const stepDuration = new Date(stepEndTime).getTime() - new Date(stepStartTime).getTime();

          stepResults.push({
            id: step.id,
            status: 'passed' as const,
            startTime: stepStartTime,
            endTime: stepEndTime,
            duration: stepDuration,
            actualResult,
            logs: [`API step executed: ${step.description}`],
            metrics: { responseTime: stepDuration }
          });

          logs.push(`Step ${step.id} completed: ${step.description}`);
          
          if (step.action.startsWith('api:')) {
            metrics.networkCalls++;
          }

        } catch (error) {
          const stepEndTime = new Date().toISOString();
          const stepDuration = new Date(stepEndTime).getTime() - new Date(stepStartTime).getTime();

          stepResults.push({
            id: step.id,
            status: 'failed' as const,
            startTime: stepStartTime,
            endTime: stepEndTime,
            duration: stepDuration,
            error: error instanceof Error ? error.message : String(error),
            logs: [`API step failed: ${step.description}`, `Error: ${error}`],
            metrics: { responseTime: stepDuration }
          });

          logs.push(`Step ${step.id} failed: ${error}`);
          throw error; // Stop execution on failure
        }
      }

      const endTime = new Date().toISOString();
      const duration = new Date(endTime).getTime() - new Date(startTime).getTime();

      return {
        id: resultId,
        testId: test.id,
        status: 'passed',
        startTime,
        endTime,
        duration,
        environment: environment.name,
        steps: stepResults,
        logs,
        metrics: {
          ...metrics,
          responseTime: duration
        }
      };

    } catch (error) {
      const endTime = new Date().toISOString();
      const duration = new Date(endTime).getTime() - new Date(startTime).getTime();

      return {
        id: resultId,
        testId: test.id,
        status: 'failed',
        startTime,
        endTime,
        duration,
        environment: environment.name,
        steps: stepResults,
        error: error instanceof Error ? error.message : String(error),
        stackTrace: error instanceof Error ? error.stack : undefined,
        logs,
        metrics: {
          networkCalls: 0,
          databaseQueries: 0,
          responseTime: duration
        }
      };
    }
  }

  /**
   * Execute test suite (delegates to orchestrator)
   */
  async runSuite(suite: TestSuite, environment: TestEnvironment): Promise<TestExecutionSummary> {
    throw new Error('Suite execution should be handled by TestOrchestrator');
  }

  /**
   * Execute API test step
   */
  private async executeAPIStep(step: any, environment: TestEnvironment): Promise<string> {
    const stepData = this.parseAPIAction(step.action);
    
    switch (stepData.type) {
      case 'request':
        return await this.executeRequest(stepData.request, step, environment);
        
      case 'validate':
        return await this.executeValidation(stepData.assertions, step);
        
      case 'extract':
        return await this.executeExtraction(stepData.extraction, step);
        
      default:
        throw new Error(`Unknown API step type: ${stepData.type}`);
    }
  }

  /**
   * Execute HTTP request
   */
  private async executeRequest(
    requestConfig: HttpRequest, 
    step: any, 
    environment: TestEnvironment
  ): Promise<string> {
    const startTime = Date.now();
    
    // Build URL
    let url = requestConfig.url;
    if (url.startsWith('/') && environment.apiUrl) {
      url = `${environment.apiUrl}${url}`;
    }

    // Add query parameters
    if (requestConfig.query) {
      const queryString = new URLSearchParams(requestConfig.query).toString();
      url += (url.includes('?') ? '&' : '?') + queryString;
    }

    // Merge headers
    const headers = {
      ...this.config.defaultHeaders,
      ...requestConfig.headers,
      ...step.data?.headers
    };

    // Add authentication
    if (requestConfig.auth) {
      this.addAuthentication(headers, requestConfig.auth, environment);
    }

    // Prepare request
    const request: HttpRequest = {
      method: requestConfig.method,
      url,
      headers,
      body: requestConfig.body || step.data?.body,
      timeout: requestConfig.timeout || step.timeout || this.config.timeout
    };

    try {
      // Make HTTP request
      const response = await this.makeRequest(request);
      const duration = Date.now() - startTime;

      // Store response for validation
      step._response = response;
      step._requestDuration = duration;

      // Validate response if configured
      if (step.data?.assertions) {
        await this.validateResponse(response, step.data.assertions);
      }

      return `${requestConfig.method} ${url} → ${response.status} ${response.statusText} (${duration}ms)`;

    } catch (error) {
      const duration = Date.now() - startTime;
      step._requestDuration = duration;
      throw new Error(`HTTP request failed: ${error instanceof Error ? error.message : error}`);
    }
  }

  /**
   * Execute response validation
   */
  private async executeValidation(assertions: APIAssertion[], step: any): Promise<string> {
    const response = step._response as HttpResponse;
    if (!response) {
      throw new Error('No response available for validation. Execute request first.');
    }

    const results: string[] = [];

    for (const assertion of assertions) {
      const result = await this.validateAssertion(assertion, response);
      results.push(result);
    }

    return `Validated ${assertions.length} assertions: ${results.join(', ')}`;
  }

  /**
   * Execute data extraction
   */
  private async executeExtraction(extraction: any, step: any): Promise<string> {
    const response = step._response as HttpResponse;
    if (!response) {
      throw new Error('No response available for extraction. Execute request first.');
    }

    const extracted: Record<string, any> = {};

    // Extract from response body
    if (extraction.body) {
      for (const [key, path] of Object.entries(extraction.body)) {
        extracted[key] = this.extractFromObject(response.body, path as string);
      }
    }

    // Extract from response headers
    if (extraction.headers) {
      for (const [key, headerName] of Object.entries(extraction.headers)) {
        extracted[key] = response.headers[headerName as string];
      }
    }

    // Store extracted values for use in subsequent steps
    step._extracted = extracted;

    const extractedKeys = Object.keys(extracted);
    return `Extracted ${extractedKeys.length} values: ${extractedKeys.join(', ')}`;
  }

  /**
   * Make HTTP request
   */
  private async makeRequest(request: HttpRequest): Promise<HttpResponse> {
    const startTime = Date.now();

    // Mock implementation - in practice would use fetch or axios
    console.log(`Making ${request.method} request to ${request.url}`);

    // Simulate network delay
    await new Promise(resolve => setTimeout(resolve, Math.random() * 100));

    // Mock response based on request
    const mockResponse: HttpResponse = {
      status: this.getMockStatus(request),
      statusText: 'OK',
      headers: {
        'content-type': 'application/json',
        'x-request-id': uuidv4()
      },
      body: this.getMockResponseBody(request),
      size: 1024,
      time: Date.now() - startTime,
      redirects: 0
    };

    // Validate status if function provided
    if (request.validateStatus && !request.validateStatus(mockResponse.status)) {
      throw new Error(`Request failed with status ${mockResponse.status}`);
    }

    return mockResponse;
  }

  /**
   * Generate mock status code
   */
  private getMockStatus(request: HttpRequest): number {
    // Simple mock logic
    if (request.url.includes('/error')) return 500;
    if (request.url.includes('/notfound')) return 404;
    if (request.url.includes('/unauthorized')) return 401;
    if (request.method === 'POST') return 201;
    return 200;
  }

  /**
   * Generate mock response body
   */
  private getMockResponseBody(request: HttpRequest): any {
    if (request.url.includes('/users')) {
      return {
        id: 123,
        name: 'Test User',
        email: 'test@example.com',
        createdAt: new Date().toISOString()
      };
    }

    if (request.url.includes('/health')) {
      return { status: 'healthy', timestamp: new Date().toISOString() };
    }

    return { message: 'Success', data: null };
  }

  /**
   * Add authentication to headers
   */
  private addAuthentication(
    headers: Record<string, string>, 
    auth: HttpRequest['auth'], 
    environment: TestEnvironment
  ): void {
    if (!auth) return;

    switch (auth.type) {
      case 'basic':
        const basicAuth = Buffer.from(
          `${auth.credentials.username}:${auth.credentials.password}`
        ).toString('base64');
        headers['Authorization'] = `Basic ${basicAuth}`;
        break;

      case 'bearer':
        const token = auth.credentials.token || environment.variables.API_TOKEN;
        headers['Authorization'] = `Bearer ${token}`;
        break;

      case 'apikey':
        const apiKey = auth.credentials.apiKey || environment.variables.API_KEY;
        const headerName = auth.credentials.headerName || 'X-API-Key';
        headers[headerName] = apiKey;
        break;

      case 'oauth2':
        // OAuth2 implementation would be more complex
        const accessToken = auth.credentials.accessToken;
        headers['Authorization'] = `Bearer ${accessToken}`;
        break;
    }
  }

  /**
   * Validate response against assertion
   */
  private async validateAssertion(assertion: APIAssertion, response: HttpResponse): Promise<string> {
    let actualValue: any;
    
    // Get actual value based on assertion type
    switch (assertion.type) {
      case 'status':
        actualValue = response.status;
        break;
        
      case 'header':
        if (!assertion.field) throw new Error('Header assertion requires field name');
        actualValue = response.headers[assertion.field];
        break;
        
      case 'body':
        if (assertion.field) {
          actualValue = this.extractFromObject(response.body, assertion.field);
        } else {
          actualValue = response.body;
        }
        break;
        
      case 'performance':
        actualValue = response.time;
        break;
        
      case 'schema':
        return this.validateSchema(response, assertion);
        
      default:
        throw new Error(`Unknown assertion type: ${assertion.type}`);
    }

    // Apply operator
    const isValid = this.applyOperator(actualValue, assertion.operator, assertion.expected);
    
    if (!isValid) {
      const message = assertion.message || 
        `${assertion.type} ${assertion.operator} ${assertion.expected}, got ${actualValue}`;
      throw new Error(`Assertion failed: ${message}`);
    }

    return `${assertion.type} ${assertion.operator} ${assertion.expected} ✓`;
  }

  /**
   * Apply comparison operator
   */
  private applyOperator(actual: any, operator: string, expected: any): boolean {
    switch (operator) {
      case 'equals':
        return actual === expected;
      case 'contains':
        return String(actual).includes(String(expected));
      case 'matches':
        return new RegExp(expected).test(String(actual));
      case 'gt':
        return Number(actual) > Number(expected);
      case 'lt':
        return Number(actual) < Number(expected);
      case 'gte':
        return Number(actual) >= Number(expected);
      case 'lte':
        return Number(actual) <= Number(expected);
      case 'exists':
        return actual !== undefined && actual !== null;
      case 'not_exists':
        return actual === undefined || actual === null;
      default:
        throw new Error(`Unknown operator: ${operator}`);
    }
  }

  /**
   * Validate response schema
   */
  private validateSchema(response: HttpResponse, assertion: APIAssertion): string {
    // Simple schema validation - in practice would use ajv or similar
    const schema = assertion.expected as ResponseSchema;
    
    if (schema.type === 'json') {
      if (typeof response.body !== 'object') {
        throw new Error('Expected JSON response');
      }
      
      if (schema.required) {
        for (const field of schema.required) {
          if (!(field in response.body)) {
            throw new Error(`Required field missing: ${field}`);
          }
        }
      }
    }

    return 'Schema validation passed ✓';
  }

  /**
   * Extract value from object using path
   */
  private extractFromObject(obj: any, path: string): any {
    if (!path) return obj;
    
    const parts = path.split('.');
    let current = obj;
    
    for (const part of parts) {
      if (current === null || current === undefined) {
        return undefined;
      }
      
      // Handle array indices
      const arrayMatch = part.match(/^(\w+)\[(\d+)\]$/);
      if (arrayMatch) {
        const [, key, index] = arrayMatch;
        current = current[key]?.[parseInt(index)];
      } else {
        current = current[part];
      }
    }
    
    return current;
  }

  /**
   * Parse API action string
   */
  private parseAPIAction(action: string): any {
    // Parse action strings like:
    // "api:request:GET:/users"
    // "api:validate:status:200"
    // "api:extract:body.id"
    
    const parts = action.split(':');
    if (parts[0] !== 'api') {
      throw new Error(`Invalid API action: ${action}`);
    }

    const type = parts[1];
    
    switch (type) {
      case 'request':
        return {
          type: 'request',
          request: {
            method: (parts[2] || 'GET') as HttpMethod,
            url: parts[3] || '/'
          }
        };
        
      case 'validate':
        return {
          type: 'validate',
          assertions: [{
            type: parts[2] || 'status',
            operator: 'equals',
            expected: parts[3] ? (isNaN(Number(parts[3])) ? parts[3] : Number(parts[3])) : 200
          }]
        };
        
      case 'extract':
        return {
          type: 'extract',
          extraction: {
            body: { extracted_value: parts[2] || 'id' }
          }
        };
        
      default:
        throw new Error(`Unknown API action type: ${type}`);
    }
  }

  /**
   * Check if action is API step
   */
  private isAPIStep(action: string): boolean {
    return action.startsWith('api:');
  }

  /**
   * Before test hook
   */
  async beforeTest?(test: TestCase): Promise<void> {
    console.log(`API: Starting test ${test.name}`);
  }

  /**
   * After test hook
   */
  async afterTest?(test: TestCase, result: TestResult): Promise<void> {
    console.log(`API: Completed test ${test.name} with status ${result.status}`);
    
    // Log performance metrics
    const avgResponseTime = result.steps.reduce((sum, step) => 
      sum + (step.metrics?.responseTime || 0), 0) / result.steps.length;
    
    if (avgResponseTime > 0) {
      console.log(`API: Average response time: ${avgResponseTime.toFixed(2)}ms`);
    }
  }
}