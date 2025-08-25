/**
 * Code Generation Agent
 * Phase 4 of ae-framework: Automated code generation from tests and specifications
 */
export interface CodeGenerationRequest {
    tests: TestFile[];
    specifications?: Specification;
    architecture?: ArchitecturePattern;
    language: 'typescript' | 'javascript' | 'python' | 'go' | 'rust' | 'elixir';
    framework?: string;
    style?: CodingStyle;
}
export interface TestFile {
    path: string;
    content: string;
    type: 'unit' | 'integration' | 'e2e';
}
export interface Specification {
    openapi?: string;
    tla?: string;
    contracts?: Contract[];
    requirements?: string[];
}
export interface Contract {
    name: string;
    preconditions: string[];
    postconditions: string[];
    invariants: string[];
}
export interface ArchitecturePattern {
    pattern: 'mvc' | 'hexagonal' | 'clean' | 'ddd' | 'microservice';
    layers?: Layer[];
    dependencies?: Dependency[];
}
export interface Layer {
    name: string;
    responsibilities: string[];
    allowedDependencies: string[];
}
export interface Dependency {
    from: string;
    to: string;
    type: 'uses' | 'implements' | 'extends';
}
export interface CodingStyle {
    naming: 'camelCase' | 'snake_case' | 'PascalCase';
    indentation: 'spaces' | 'tabs';
    indentSize?: number;
    maxLineLength?: number;
    preferConst?: boolean;
    preferArrowFunctions?: boolean;
}
export interface GeneratedCode {
    files: CodeFile[];
    structure: ProjectStructure;
    dependencies: string[];
    testResults: TestResult[];
    coverage: number;
    suggestions: string[];
}
export interface CodeFile {
    path: string;
    content: string;
    purpose: string;
    tests: string[];
}
export interface ProjectStructure {
    directories: string[];
    entryPoint: string;
    configFiles: ConfigFile[];
}
export interface ConfigFile {
    name: string;
    content: string;
    purpose: string;
}
export interface TestResult {
    test: string;
    status: 'passing' | 'failing' | 'pending';
    error?: string;
}
export declare class CodeGenerationAgent {
    /**
     * Generate code from tests (TDD approach)
     */
    generateCodeFromTests(request: CodeGenerationRequest): Promise<GeneratedCode>;
    /**
     * Generate code from OpenAPI specification
     */
    generateFromOpenAPI(spec: string, options: {
        framework: 'fastify' | 'express' | 'koa';
        database?: 'postgres' | 'mongodb' | 'mysql';
        includeValidation?: boolean;
        includeAuth?: boolean;
    }): Promise<GeneratedCode>;
    /**
     * Apply design patterns to code
     */
    applyDesignPatterns(code: string, patterns: string[]): Promise<string>;
    /**
     * Optimize code for performance
     */
    optimizePerformance(code: string, metrics: {
        targetResponseTime?: number;
        targetMemoryUsage?: number;
        targetCPUUsage?: number;
    }): Promise<{
        optimizedCode: string;
        improvements: PerformanceImprovement[];
        benchmarks: Benchmark[];
    }>;
    /**
     * Add security features to code
     */
    addSecurityFeatures(code: string, requirements: {
        authentication?: 'jwt' | 'oauth' | 'basic';
        authorization?: 'rbac' | 'abac' | 'simple';
        encryption?: boolean;
        rateLimit?: boolean;
        cors?: boolean;
    }): Promise<string>;
    /**
     * Generate error handling code
     */
    generateErrorHandling(code: string, strategy: {
        type: 'try-catch' | 'result-type' | 'middleware';
        logging?: boolean;
        recovery?: boolean;
        userFriendly?: boolean;
    }): Promise<string>;
    /**
     * Generate database access layer
     */
    generateDataAccessLayer(schema: DatabaseSchema, options: {
        orm?: 'typeorm' | 'prisma' | 'sequelize' | 'none';
        database: 'postgres' | 'mysql' | 'mongodb' | 'sqlite';
        includeTransactions?: boolean;
        includeMigrations?: boolean;
    }): Promise<GeneratedCode>;
    /**
     * Refactor existing code
     */
    refactorCode(code: string, goals: {
        reduceComplexity?: boolean;
        improveDRY?: boolean;
        improveNaming?: boolean;
        extractMethods?: boolean;
        introducePatterns?: string[];
    }): Promise<{
        refactoredCode: string;
        changes: RefactoringChange[];
        metrics: CodeMetrics;
    }>;
    private analyzeTests;
    private designArchitecture;
    private generateImplementation;
    private generateFunctionImplementation;
    private generateElixirFunction;
    private generatePhoenixModule;
    private generateTSFunction;
    private generatePythonFunction;
    private generateRustFunction;
    private generateGoFunction;
    private getFileExtension;
    private getTestExtension;
    private getSourceDirectory;
    private getTestDirectory;
    private capitalize;
    private runTests;
    private calculateCoverage;
    private generateSuggestions;
    private generateValidationMiddleware;
    private generateAuthMiddleware;
    private generateServerSetup;
    private parseOpenAPI;
    private generateRouteHandler;
    private generateModel;
    private createProjectStructure;
    private identifyDependencies;
    private getFrameworkDependencies;
    private applySingletonPattern;
    private applyFactoryPattern;
    private applyObserverPattern;
    private applyStrategyPattern;
    private applyDecoratorPattern;
    private applyRepositoryPattern;
    private identifyBottlenecks;
    private optimizeBottleneck;
    private applyOptimization;
    private runBenchmarks;
    private addAuthentication;
    private addAuthorization;
    private addEncryption;
    private addRateLimiting;
    private addCORS;
    private wrapInTryCatch;
    private convertToResultType;
    private addErrorMiddleware;
    private addErrorLogging;
    private addRecoveryMechanisms;
    private addUserFriendlyErrors;
    private generateEntity;
    private generateRepository;
    private generateDatabaseConnection;
    private generateMigrations;
    private generateTransactionHelpers;
    private createDataLayerStructure;
    private getORMDependencies;
    private reduceComplexity;
    private eliminateDuplication;
    private improveNaming;
    private extractMethods;
    private calculateMetrics;
}
interface DatabaseSchema {
    tables: Table[];
    relations: Relation[];
}
interface Table {
    name: string;
    columns: Column[];
    indexes: Index[];
}
interface Column {
    name: string;
    type: string;
    nullable: boolean;
    primary?: boolean;
    unique?: boolean;
}
interface Index {
    name: string;
    columns: string[];
    unique: boolean;
}
interface Relation {
    from: string;
    to: string;
    type: 'one-to-one' | 'one-to-many' | 'many-to-many';
}
interface PerformanceImprovement {
    location: string;
    type: string;
    description: string;
    impact: 'high' | 'medium' | 'low';
}
interface Benchmark {
    name: string;
    before: number;
    after: number;
    improvement: number;
}
interface RefactoringChange {
    type: string;
    location: string;
    description: string;
}
interface CodeMetrics {
    complexity: number;
    maintainability: number;
    duplication: number;
    testCoverage: number;
}
export {};
