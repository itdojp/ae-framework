/**
 * End-to-End Test Runner
 * Phase 2.3: Browser-based E2E test execution with Playwright integration
 */
/**
 * Test step result interface
 */
export interface TestStepResult {
    stepIndex: number;
    action: string;
    status: 'success' | 'error';
    message: string;
    duration: number;
    screenshot?: string;
}
import { TestRunner, TestCase, TestSuite, TestEnvironment, TestResult, TestExecutionSummary, TestCategory } from '../types.js';
export type BrowserType = 'chromium' | 'firefox' | 'webkit';
export interface E2EConfig {
    browser: BrowserType;
    headless: boolean;
    viewport: {
        width: number;
        height: number;
    };
    timeout: number;
    retries: number;
    screenshots: boolean;
    video: boolean;
    trace: boolean;
    slowMo: number;
}
export interface BrowserPage {
    goto(url: string): Promise<void>;
    click(selector: string): Promise<void>;
    fill(selector: string, value: string): Promise<void>;
    selectOption(selector: string, value: string): Promise<void>;
    waitForSelector(selector: string, timeout?: number): Promise<void>;
    waitForTimeout(timeout: number): Promise<void>;
    screenshot(options?: {
        path?: string;
        fullPage?: boolean;
    }): Promise<Buffer>;
    textContent(selector: string): Promise<string | null>;
    getAttribute(selector: string, name: string): Promise<string | null>;
    isVisible(selector: string): Promise<boolean>;
    locator(selector: string): any;
    evaluate(fn: () => any): Promise<any>;
    reload(): Promise<void>;
    close(): Promise<void>;
}
export interface BrowserContext {
    newPage(): Promise<BrowserPage>;
    close(): Promise<void>;
}
export interface Browser {
    newContext(options?: any): Promise<BrowserContext>;
    close(): Promise<void>;
}
export declare class E2ETestRunner implements TestRunner {
    readonly id = "e2e-runner";
    readonly name = "End-to-End Test Runner";
    readonly category: TestCategory;
    private config;
    private browser;
    private context;
    private currentPage;
    constructor(config: E2EConfig);
    /**
     * Check if runner can execute test
     */
    canRun(test: TestCase): boolean;
    /**
     * Setup browser environment
     */
    setup(environment: TestEnvironment): Promise<void>;
    /**
     * Teardown browser environment
     */
    teardown(environment: TestEnvironment): Promise<void>;
    /**
     * Execute single test
     */
    runTest(test: TestCase, environment: TestEnvironment): Promise<TestResult>;
    /**
     * Execute test suite (delegates to orchestrator)
     */
    runSuite(suite: TestSuite, environment: TestEnvironment): Promise<TestExecutionSummary>;
    /**
     * Execute individual test step
     */
    private executeStep;
    /**
     * Execute verification step
     */
    private executeVerification;
    /**
     * Execute custom step
     */
    private executeCustomStep;
    /**
     * Parse step action string
     */
    private parseStepAction;
    /**
     * Check if action is E2E step
     */
    private isE2EStep;
    /**
     * Capture screenshot
     */
    private captureScreenshot;
    /**
     * Launch browser (placeholder implementation)
     */
    private launchBrowser;
    /**
     * Create mock page for testing
     */
    private createMockPage;
    /**
     * Before test hook
     */
    beforeTest?(test: TestCase): Promise<void>;
    /**
     * After test hook
     */
    afterTest?(test: TestCase, result: TestResult): Promise<void>;
}
