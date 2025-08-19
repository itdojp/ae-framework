/**
 * End-to-End Test Runner
 * Phase 2.3: Browser-based E2E test execution with Playwright integration
 */

import { v4 as uuidv4 } from 'uuid';
import { promises as fs } from 'fs';
import { join } from 'path';
import {
  TestRunner,
  TestCase,
  TestSuite,
  TestEnvironment,
  TestResult,
  TestExecutionSummary,
  TestCategory,
  E2ETestStep
} from '../types.js';

// Browser types
export type BrowserType = 'chromium' | 'firefox' | 'webkit';

// E2E configuration
export interface E2EConfig {
  browser: BrowserType;
  headless: boolean;
  viewport: { width: number; height: number };
  timeout: number;
  retries: number;
  screenshots: boolean;
  video: boolean;
  trace: boolean;
  slowMo: number;
}

// Browser page interface (simplified)
export interface BrowserPage {
  goto(url: string): Promise<void>;
  click(selector: string): Promise<void>;
  fill(selector: string, value: string): Promise<void>;
  selectOption(selector: string, value: string): Promise<void>;
  waitForSelector(selector: string, timeout?: number): Promise<void>;
  waitForTimeout(timeout: number): Promise<void>;
  screenshot(options?: { path?: string; fullPage?: boolean }): Promise<Buffer>;
  textContent(selector: string): Promise<string | null>;
  getAttribute(selector: string, name: string): Promise<string | null>;
  isVisible(selector: string): Promise<boolean>;
  locator(selector: string): any;
  evaluate(fn: () => any): Promise<any>;
  reload(): Promise<void>;
  close(): Promise<void>;
}

// Browser context interface
export interface BrowserContext {
  newPage(): Promise<BrowserPage>;
  close(): Promise<void>;
}

// Browser interface
export interface Browser {
  newContext(options?: any): Promise<BrowserContext>;
  close(): Promise<void>;
}

export class E2ETestRunner implements TestRunner {
  readonly id = 'e2e-runner';
  readonly name = 'End-to-End Test Runner';
  readonly category: TestCategory = 'e2e';

  private config: E2EConfig;
  private browser: Browser | null = null;
  private context: BrowserContext | null = null;
  private currentPage: BrowserPage | null = null;

  constructor(config: E2EConfig) {
    this.config = config;
  }

  /**
   * Check if runner can execute test
   */
  canRun(test: TestCase): boolean {
    return test.category === 'e2e' && 
           test.steps.some(step => this.isE2EStep(step.action));
  }

  /**
   * Setup browser environment
   */
  async setup(environment: TestEnvironment): Promise<void> {
    try {
      // Initialize browser (in practice, would use Playwright or Selenium)
      this.browser = await this.launchBrowser();
      this.context = await this.browser.newContext({
        viewport: this.config.viewport,
        recordVideo: this.config.video ? { dir: './test-results/videos' } : undefined,
        recordTrace: this.config.trace ? './test-results/traces' : undefined
      });

      // Set default timeout
      // this.context.setDefaultTimeout(this.config.timeout);
      
    } catch (error) {
      throw new Error(`Failed to setup E2E environment: ${error}`);
    }
  }

  /**
   * Teardown browser environment
   */
  async teardown(environment: TestEnvironment): Promise<void> {
    try {
      if (this.currentPage) {
        await this.currentPage.close();
        this.currentPage = null;
      }
      
      if (this.context) {
        await this.context.close();
        this.context = null;
      }
      
      if (this.browser) {
        await this.browser.close();
        this.browser = null;
      }
    } catch (error) {
      console.error('Error during E2E teardown:', error);
    }
  }

  /**
   * Execute single test
   */
  async runTest(test: TestCase, environment: TestEnvironment): Promise<TestResult> {
    const startTime = new Date().toISOString();
    const resultId = uuidv4();
    const stepResults: any[] = [];
    const screenshots: string[] = [];
    const logs: string[] = [];
    
    if (!this.context) {
      throw new Error('E2E environment not initialized. Call setup() first.');
    }

    try {
      // Create new page for test
      this.currentPage = await this.context.newPage();

      // Execute preconditions
      for (const precondition of test.preconditions) {
        logs.push(`Precondition: ${precondition}`);
      }

      // Execute test steps
      for (const step of test.steps) {
        const stepStartTime = new Date().toISOString();
        
        try {
          // Execute step based on action type
          const actualResult = await this.executeStep(step, environment);
          
          const stepEndTime = new Date().toISOString();
          const stepDuration = new Date(stepEndTime).getTime() - new Date(stepStartTime).getTime();

          // Capture screenshot if needed
          let screenshotPath: string | undefined;
          if (this.config.screenshots || step.data?.screenshot) {
            screenshotPath = await this.captureScreenshot(test.id, step.id);
            screenshots.push(screenshotPath);
          }

          stepResults.push({
            id: step.id,
            status: 'passed' as const,
            startTime: stepStartTime,
            endTime: stepEndTime,
            duration: stepDuration,
            actualResult,
            screenshots: screenshotPath ? [screenshotPath] : [],
            logs: [`Step executed: ${step.description}`],
            metrics: {}
          });

          logs.push(`Step ${step.id} completed: ${step.description}`);

        } catch (error) {
          const stepEndTime = new Date().toISOString();
          const stepDuration = new Date(stepEndTime).getTime() - new Date(stepStartTime).getTime();
          
          // Capture screenshot on failure
          const screenshotPath = await this.captureScreenshot(test.id, step.id, 'failure');
          screenshots.push(screenshotPath);

          stepResults.push({
            id: step.id,
            status: 'failed' as const,
            startTime: stepStartTime,
            endTime: stepEndTime,
            duration: stepDuration,
            error: error instanceof Error ? error.message : String(error),
            screenshots: [screenshotPath],
            logs: [`Step failed: ${step.description}`, `Error: ${error}`],
            metrics: {}
          });

          logs.push(`Step ${step.id} failed: ${error}`);
          
          // Stop execution on step failure
          throw error;
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
        screenshots,
        logs,
        metrics: {
          networkCalls: 0, // Would be tracked in real implementation
          databaseQueries: 0,
          renderTime: duration
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
        screenshots,
        logs: [...logs, `Test failed: ${error}`],
        metrics: {
          networkCalls: 0,
          databaseQueries: 0,
          renderTime: duration
        }
      };
    } finally {
      // Close page
      if (this.currentPage) {
        await this.currentPage.close();
        this.currentPage = null;
      }
    }
  }

  /**
   * Execute test suite (delegates to orchestrator)
   */
  async runSuite(suite: TestSuite, environment: TestEnvironment): Promise<TestExecutionSummary> {
    throw new Error('Suite execution should be handled by TestOrchestrator');
  }

  /**
   * Execute individual test step
   */
  private async executeStep(step: any, environment: TestEnvironment): Promise<string> {
    if (!this.currentPage) {
      throw new Error('No active page for step execution');
    }

    const page = this.currentPage;
    const stepData = this.parseStepAction(step.action);

    // Add slow motion if configured
    if (this.config.slowMo > 0) {
      await page.waitForTimeout(this.config.slowMo);
    }

    switch (stepData.type) {
      case 'navigate':
        const url = step.data?.url || stepData.value || environment.baseUrl;
        await page.goto(url);
        return `Navigated to ${url}`;

      case 'click':
        const clickSelector = step.data?.selector || stepData.selector;
        if (!clickSelector) throw new Error('Click action requires selector');
        await page.waitForSelector(clickSelector, step.timeout || this.config.timeout);
        await page.click(clickSelector);
        return `Clicked element: ${clickSelector}`;

      case 'type':
        const typeSelector = step.data?.selector || stepData.selector;
        const typeValue = step.data?.value || stepData.value;
        if (!typeSelector || !typeValue) throw new Error('Type action requires selector and value');
        await page.waitForSelector(typeSelector, step.timeout || this.config.timeout);
        await page.fill(typeSelector, typeValue);
        return `Typed '${typeValue}' into ${typeSelector}`;

      case 'select':
        const selectSelector = step.data?.selector || stepData.selector;
        const selectValue = step.data?.value || stepData.value;
        if (!selectSelector || !selectValue) throw new Error('Select action requires selector and value');
        await page.waitForSelector(selectSelector, step.timeout || this.config.timeout);
        await page.selectOption(selectSelector, selectValue);
        return `Selected '${selectValue}' in ${selectSelector}`;

      case 'wait':
        const waitTime = step.data?.timeout || stepData.timeout || 1000;
        await page.waitForTimeout(waitTime);
        return `Waited ${waitTime}ms`;

      case 'verify':
        const verifyResult = await this.executeVerification(page, step);
        return verifyResult;

      case 'screenshot':
        const screenshotPath = await this.captureScreenshot(step.id || 'manual', Date.now().toString());
        return `Screenshot saved: ${screenshotPath}`;

      case 'custom':
        return await this.executeCustomStep(page, step, environment);

      default:
        throw new Error(`Unknown step type: ${stepData.type}`);
    }
  }

  /**
   * Execute verification step
   */
  private async executeVerification(page: BrowserPage, step: any): Promise<string> {
    const validation = step.validation;
    if (!validation) {
      throw new Error('Verify step requires validation configuration');
    }

    const selector = step.data?.selector || step.selector;

    switch (validation.type) {
      case 'text':
        if (!selector) throw new Error('Text verification requires selector');
        const actualText = await page.textContent(selector);
        const expectedText = validation.expected;
        
        if (actualText !== expectedText) {
          throw new Error(`Text verification failed: expected '${expectedText}', got '${actualText}'`);
        }
        return `Text verification passed: '${actualText}'`;

      case 'attribute':
        if (!selector) throw new Error('Attribute verification requires selector');
        const attributeName = validation.attribute || 'value';
        const actualValue = await page.getAttribute(selector, attributeName);
        const expectedValue = validation.expected;
        
        if (actualValue !== expectedValue) {
          throw new Error(`Attribute verification failed: expected '${expectedValue}', got '${actualValue}'`);
        }
        return `Attribute verification passed: ${attributeName}='${actualValue}'`;

      case 'exists':
        if (!selector) throw new Error('Exists verification requires selector');
        const exists = await page.isVisible(selector);
        const shouldExist = validation.expected;
        
        if (exists !== shouldExist) {
          throw new Error(`Exists verification failed: expected ${shouldExist}, element exists: ${exists}`);
        }
        return `Exists verification passed: element ${exists ? 'exists' : 'does not exist'}`;

      case 'count':
        if (!selector) throw new Error('Count verification requires selector');
        const elements = await page.locator(selector);
        const actualCount = await elements.count();
        const expectedCount = validation.expected;
        
        if (actualCount !== expectedCount) {
          throw new Error(`Count verification failed: expected ${expectedCount}, got ${actualCount}`);
        }
        return `Count verification passed: found ${actualCount} elements`;

      default:
        throw new Error(`Unknown validation type: ${validation.type}`);
    }
  }

  /**
   * Execute custom step
   */
  private async executeCustomStep(
    page: BrowserPage, 
    step: any, 
    environment: TestEnvironment
  ): Promise<string> {
    // This would be extended to support custom step implementations
    const customAction = step.data?.customAction;
    
    if (customAction === 'scroll_to_bottom') {
      await page.evaluate(() => window.scrollTo(0, document.body.scrollHeight));
      return 'Scrolled to bottom of page';
    }
    
    if (customAction === 'refresh') {
      await page.reload();
      return 'Page refreshed';
    }
    
    throw new Error(`Unknown custom action: ${customAction}`);
  }

  /**
   * Parse step action string
   */
  private parseStepAction(action: string): E2ETestStep {
    // Simple parser for action strings like "click:button#submit" or "type:input[name=username]:testuser"
    const parts = action.split(':');
    const type = parts[0] as any;
    const selector = parts[1];
    const value = parts[2];
    const timeout = parts[3] ? parseInt(parts[3]) : undefined;

    return {
      type,
      selector,
      value,
      timeout,
      description: action
    };
  }

  /**
   * Check if action is E2E step
   */
  private isE2EStep(action: string): boolean {
    const e2eActions = ['navigate', 'click', 'type', 'select', 'wait', 'verify', 'screenshot', 'custom'];
    return e2eActions.some(e2eAction => action.startsWith(e2eAction));
  }

  /**
   * Capture screenshot
   */
  private async captureScreenshot(
    testId: string, 
    stepId: string, 
    type: string = 'step'
  ): Promise<string> {
    if (!this.currentPage) {
      throw new Error('No active page for screenshot');
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const fileName = `${testId}_${stepId}_${type}_${timestamp}.png`;
    const filePath = join('./test-results/screenshots', fileName);

    // Ensure directory exists
    await fs.mkdir('./test-results/screenshots', { recursive: true });

    // Capture screenshot
    const buffer = await this.currentPage.screenshot({ 
      path: filePath, 
      fullPage: true 
    });

    return filePath;
  }

  /**
   * Launch browser (placeholder implementation)
   */
  private async launchBrowser(): Promise<Browser> {
    // In real implementation, would use Playwright or Selenium
    // This is a mock implementation
    return {
      newContext: async (options?: any): Promise<BrowserContext> => {
        return {
          newPage: async (): Promise<BrowserPage> => {
            return this.createMockPage();
          },
          close: async (): Promise<void> => {
            // Mock close
          }
        };
      },
      close: async (): Promise<void> => {
        // Mock close
      }
    };
  }

  /**
   * Create mock page for testing
   */
  private createMockPage(): BrowserPage {
    return {
      goto: async (url: string): Promise<void> => {
        console.log(`Mock: Navigate to ${url}`);
      },
      click: async (selector: string): Promise<void> => {
        console.log(`Mock: Click ${selector}`);
      },
      fill: async (selector: string, value: string): Promise<void> => {
        console.log(`Mock: Fill ${selector} with ${value}`);
      },
      selectOption: async (selector: string, value: string): Promise<void> => {
        console.log(`Mock: Select ${value} in ${selector}`);
      },
      waitForSelector: async (selector: string, timeout?: number): Promise<void> => {
        console.log(`Mock: Wait for ${selector}`);
      },
      waitForTimeout: async (timeout: number): Promise<void> => {
        await new Promise(resolve => setTimeout(resolve, Math.min(timeout, 100))); // Speed up for testing
      },
      screenshot: async (options?: { path?: string; fullPage?: boolean }): Promise<Buffer> => {
        const mockImageData = Buffer.from('mock-screenshot-data');
        if (options?.path) {
          await fs.writeFile(options.path, mockImageData);
        }
        return mockImageData;
      },
      textContent: async (selector: string): Promise<string | null> => {
        return `Mock text content for ${selector}`;
      },
      getAttribute: async (selector: string, name: string): Promise<string | null> => {
        return `mock-${name}-value`;
      },
      isVisible: async (selector: string): Promise<boolean> => {
        return true; // Mock: element always visible
      },
      locator: (selector: string) => {
        return {
          count: async () => 1 // Mock: always find one element
        };
      },
      evaluate: async (fn: () => any): Promise<any> => {
        console.log('Mock: Evaluate function');
        return 'mock-evaluated-result';
      },
      reload: async (): Promise<void> => {
        console.log('Mock: Reload page');
      },
      close: async (): Promise<void> => {
        console.log('Mock: Close page');
      }
    } as any;
  }

  /**
   * Before test hook
   */
  async beforeTest?(test: TestCase): Promise<void> {
    console.log(`E2E: Starting test ${test.name}`);
  }

  /**
   * After test hook
   */
  async afterTest?(test: TestCase, result: TestResult): Promise<void> {
    console.log(`E2E: Completed test ${test.name} with status ${result.status}`);
    
    // Save test artifacts
    if (result.screenshots.length > 0) {
      console.log(`E2E: Captured ${result.screenshots.length} screenshots`);
    }
  }
}