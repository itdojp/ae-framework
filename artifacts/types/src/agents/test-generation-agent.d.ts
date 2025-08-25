/**
 * Test Generation Agent
 * 自動的にテストケースを生成し、包括的なテスト戦略を提供
 */
export interface TestGenerationRequest {
    feature: string;
    requirements?: string[];
    codeFile?: string;
    testFramework: 'vitest' | 'jest' | 'mocha' | 'exunit';
}
export interface GeneratedTest {
    testFile: string;
    testContent: string;
    testCases: TestCase[];
    coverage: TestCoverage;
    recommendations: string[];
}
export interface TestCase {
    name: string;
    type: 'unit' | 'integration' | 'e2e' | 'property' | 'contract';
    description: string;
    priority: 'critical' | 'high' | 'medium' | 'low';
    code: string;
    dataGenerators?: PropertyGenerator[];
}
export interface PropertyGenerator {
    name: string;
    type: string;
    constraints: string[];
    generator: string;
}
export interface TestCoverage {
    functional: string[];
    edgeCases: string[];
    errorHandling: string[];
    performance: string[];
    security: string[];
}
export declare class TestGenerationAgent {
    /**
     * 要件からテストケースを自動生成
     */
    generateTestsFromRequirements(request: TestGenerationRequest): Promise<GeneratedTest>;
    /**
     * コードからテストを逆生成（リバースTDD）
     */
    generateTestsFromCode(codeFile: string): Promise<GeneratedTest>;
    /**
     * Property-Based Testing の自動設計
     */
    generatePropertyTests(contract: {
        function: string;
        inputs: Array<{
            name: string;
            type: string;
            constraints?: string[];
        }>;
        outputs: {
            type: string;
            constraints?: string[];
        };
        invariants: string[];
    }): Promise<TestCase[]>;
    /**
     * BDD シナリオの自動生成
     */
    generateBDDScenarios(userStory: {
        title: string;
        asA: string;
        iWant: string;
        soThat: string;
        acceptanceCriteria: string[];
    }): Promise<string>;
    /**
     * 統合テスト戦略の立案
     */
    planIntegrationTests(architecture: {
        services: Array<{
            name: string;
            dependencies: string[];
        }>;
        dataFlow: Array<{
            from: string;
            to: string;
            data: string;
        }>;
    }): Promise<{
        testPlan: IntegrationTestPlan;
        mockStrategy: MockStrategy;
        testOrder: string[];
    }>;
    /**
     * セキュリティテストの自動生成
     */
    generateSecurityTests(endpoint: {
        path: string;
        method: string;
        authentication: boolean;
        authorization?: string[];
        inputs: any[];
    }): Promise<TestCase[]>;
    /**
     * パフォーマンステストの設計
     */
    designPerformanceTests(sla: {
        responseTime: number;
        throughput: number;
        concurrentUsers: number;
        availability: number;
    }): Promise<{
        loadTests: LoadTest[];
        stressTests: StressTest[];
        spikeTests: SpikeTest[];
        soakTests: SoakTest[];
    }>;
    private analyzeAndGenerateTestCases;
    private analyzeCode;
    private generateTestFileContent;
    private generateExUnitTestContent;
    private convertToExUnitTest;
    private toElixirModuleName;
    private generatePropertyTestCode;
    private generateArbitrary;
    private extractFunctions;
    private extractClasses;
    private calculateComplexity;
    private generateImports;
    private determineTestFilePath;
    private analyzeCoverage;
    private generateRecommendations;
    private identifyEdgeCases;
    private generateHappyPathTest;
    private generateErrorHandlingTest;
    private generateEdgeCaseTest;
    private generateTestCasesFromAnalysis;
    private generateCodeBasedRecommendations;
    private createDataGenerators;
    private detectEdgeCaseProperties;
    private criteriaToScenario;
    private generateEdgeCaseScenarios;
    private identifyCriticalPaths;
    private identifyIntegrationPoints;
    private generateUnitIntegrationTests;
    private generateServiceIntegrationTests;
    private generateE2ETests;
    private calculateIntegrationCoverage;
    private determineMockStrategy;
    private optimizeTestExecutionOrder;
    private generateInjectionTest;
    private generateAuthenticationTest;
    private generateAuthorizationTest;
    private generateXSSTest;
    private generateCSRFTest;
    private generateFuzzingTest;
    private generateLoadTests;
    private generateStressTests;
    private generateSpikeTests;
    private generateSoakTests;
    private inferFeatureName;
    private extractDependencies;
    private detectPatterns;
    private invariantToAssertion;
    private applyConstraint;
}
interface IntegrationTestPlan {
    phases: Array<{
        name: string;
        tests: any[];
    }>;
    coverage: number;
}
interface MockStrategy {
    approach: 'full' | 'partial' | 'none';
    mocks: Array<{
        service: string;
        type: string;
    }>;
}
interface LoadTest {
    name: string;
    duration: number;
    users: number;
    rampUp: number;
}
interface StressTest extends LoadTest {
    breakingPoint: boolean;
}
interface SpikeTest extends LoadTest {
    spikeMultiplier: number;
}
interface SoakTest extends LoadTest {
    sustainedDuration: number;
}
export {};
