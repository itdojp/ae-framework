/**
 * Unified types for Extended Commands
 * Provides consistent data structures across all commands
 */
export interface AnalysisTarget {
    path: string;
    type: 'file' | 'directory';
}
export interface Issue {
    type: string;
    severity: 'critical' | 'high' | 'medium' | 'low' | 'info';
    message: string;
    location?: {
        file?: string;
        line?: number;
        column?: number;
    };
}
export interface Suggestion {
    type: string;
    message: string;
    priority: 'high' | 'medium' | 'low';
    category: string;
    confidence?: number;
}
export interface Metrics {
    lines: number;
    files: number;
    complexity?: number;
    coverage?: number;
}
export interface UnifiedResult {
    target: AnalysisTarget;
    summary: string;
    issues: Issue[];
    suggestions: Suggestion[];
    metrics: Metrics;
    metadata: {
        timestamp: string;
        commandType: string;
        processingTime: number;
    };
}
export interface CodeAnalysis extends UnifiedResult {
    codeMetrics: {
        functions: number;
        classes: number;
        dependencies: string[];
        cyclomaticComplexity: number;
        cognitiveComplexity: number;
    };
    securityIssues: Issue[];
    performanceIssues: Issue[];
}
export interface DocumentationResult extends UnifiedResult {
    documentation: {
        exports: ExportedItem[];
        examples: Example[];
        dependencies: string[];
        coverage: number;
    };
    format: 'markdown' | 'jsdoc' | 'api-json';
    outputPath?: string;
}
export interface ExportedItem {
    name: string;
    type: 'function' | 'class' | 'interface' | 'type' | 'constant' | 'enum';
    signature?: string;
    description?: string;
    parameters?: Parameter[];
    returns?: ReturnValue;
}
export interface Parameter {
    name: string;
    type: string;
    description?: string;
    optional?: boolean;
    defaultValue?: string;
}
export interface ReturnValue {
    type: string;
    description?: string;
}
export interface Example {
    title: string;
    code: string;
    description?: string;
}
export interface ImprovementResult extends UnifiedResult {
    improvements: Improvement[];
    appliedCount: number;
    estimatedImpact: string;
}
export interface Improvement {
    type: 'refactor' | 'optimize' | 'simplify' | 'modernize' | 'security' | 'pattern';
    description: string;
    location: {
        line: number;
        column?: number;
    };
    original: string;
    suggested: string;
    impact: 'high' | 'medium' | 'low';
    category: 'performance' | 'readability' | 'maintainability' | 'security' | 'best-practice';
    confidence: number;
}
export interface TroubleshootResult extends UnifiedResult {
    detectedIssues: DetectedIssue[];
    diagnosis: Diagnosis[];
    solutions: Solution[];
}
export interface DetectedIssue extends Issue {
    stackTrace?: string;
    reproducible?: boolean;
    frequency?: number;
}
export interface Diagnosis {
    rootCause: string;
    affectedComponents: string[];
    impact: string;
    confidence: number;
}
export interface Solution {
    description: string;
    steps: string[];
    confidence: number;
    estimatedTime: string;
    riskLevel: 'low' | 'medium' | 'high';
    prerequisites?: string[];
}
export interface BaseCommandOptions {
    validate?: boolean;
    output?: string;
    format?: string;
    verbose?: boolean;
    dryRun?: boolean;
}
export interface AnalysisOptions extends BaseCommandOptions {
    depth?: 'shallow' | 'normal' | 'deep';
    includeTests?: boolean;
    includeSecurity?: boolean;
    includePerformance?: boolean;
    minConfidence?: number;
}
export interface DocumentationOptions extends BaseCommandOptions {
    format?: 'markdown' | 'jsdoc' | 'api-json';
    includePrivate?: boolean;
    includeExamples?: boolean;
    template?: string;
}
export interface ImprovementOptions extends BaseCommandOptions {
    category?: string;
    impact?: 'high' | 'medium' | 'low';
    apply?: boolean;
    interactive?: boolean;
}
export interface TroubleshootOptions extends BaseCommandOptions {
    auto?: boolean;
    logs?: string;
    error?: string;
    interactive?: boolean;
}
