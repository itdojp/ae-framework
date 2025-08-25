/**
 * CEGIS (Counter-Example Guided Inductive Synthesis) Types
 * Phase 2.1: Core types for failure artifacts and auto-fix system
 */
import { z } from 'zod';
export declare const FailureCategorySchema: z.ZodEnum<["contract_violation", "test_failure", "type_error", "runtime_error", "build_error", "lint_error", "security_violation", "performance_issue", "accessibility_violation", "dependency_issue"]>;
export type FailureCategory = z.infer<typeof FailureCategorySchema>;
export declare const CodeLocationSchema: z.ZodObject<{
    filePath: z.ZodString;
    startLine: z.ZodNumber;
    endLine: z.ZodNumber;
    startColumn: z.ZodOptional<z.ZodNumber>;
    endColumn: z.ZodOptional<z.ZodNumber>;
    functionName: z.ZodOptional<z.ZodString>;
    className: z.ZodOptional<z.ZodString>;
}, "strip", z.ZodTypeAny, {
    filePath?: string;
    startLine?: number;
    endLine?: number;
    startColumn?: number;
    endColumn?: number;
    functionName?: string;
    className?: string;
}, {
    filePath?: string;
    startLine?: number;
    endLine?: number;
    startColumn?: number;
    endColumn?: number;
    functionName?: string;
    className?: string;
}>;
export type CodeLocation = z.infer<typeof CodeLocationSchema>;
export declare const FailureContextSchema: z.ZodObject<{
    environment: z.ZodDefault<z.ZodString>;
    nodeVersion: z.ZodOptional<z.ZodString>;
    timestamp: z.ZodString;
    phase: z.ZodOptional<z.ZodEnum<["intent", "formal", "test", "code", "verify", "operate"]>>;
    command: z.ZodOptional<z.ZodString>;
    workingDirectory: z.ZodOptional<z.ZodString>;
    gitCommit: z.ZodOptional<z.ZodString>;
    gitBranch: z.ZodOptional<z.ZodString>;
}, "strip", z.ZodTypeAny, {
    environment?: string;
    timestamp?: string;
    command?: string;
    phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
    nodeVersion?: string;
    workingDirectory?: string;
    gitCommit?: string;
    gitBranch?: string;
}, {
    environment?: string;
    timestamp?: string;
    command?: string;
    phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
    nodeVersion?: string;
    workingDirectory?: string;
    gitCommit?: string;
    gitBranch?: string;
}>;
export type FailureContext = z.infer<typeof FailureContextSchema>;
export declare const FailureEvidenceSchema: z.ZodObject<{
    stackTrace: z.ZodOptional<z.ZodString>;
    errorMessage: z.ZodOptional<z.ZodString>;
    errorType: z.ZodOptional<z.ZodString>;
    logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metrics: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
    sourceCode: z.ZodOptional<z.ZodString>;
    testOutput: z.ZodOptional<z.ZodString>;
    buildOutput: z.ZodOptional<z.ZodString>;
    lintOutput: z.ZodOptional<z.ZodString>;
    dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    relatedFiles: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
}, "strip", z.ZodTypeAny, {
    dependencies?: string[];
    metrics?: Record<string, number>;
    logs?: string[];
    sourceCode?: string;
    stackTrace?: string;
    errorMessage?: string;
    errorType?: string;
    testOutput?: string;
    buildOutput?: string;
    lintOutput?: string;
    relatedFiles?: string[];
}, {
    dependencies?: string[];
    metrics?: Record<string, number>;
    logs?: string[];
    sourceCode?: string;
    stackTrace?: string;
    errorMessage?: string;
    errorType?: string;
    testOutput?: string;
    buildOutput?: string;
    lintOutput?: string;
    relatedFiles?: string[];
}>;
export type FailureEvidence = z.infer<typeof FailureEvidenceSchema>;
export declare const RootCauseSchema: z.ZodObject<{
    primaryCause: z.ZodString;
    contributingFactors: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    confidence: z.ZodNumber;
    reasoning: z.ZodString;
    suggestedActions: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
}, "strip", z.ZodTypeAny, {
    confidence?: number;
    primaryCause?: string;
    contributingFactors?: string[];
    reasoning?: string;
    suggestedActions?: string[];
}, {
    confidence?: number;
    primaryCause?: string;
    contributingFactors?: string[];
    reasoning?: string;
    suggestedActions?: string[];
}>;
export type RootCause = z.infer<typeof RootCauseSchema>;
export declare const RepairActionSchema: z.ZodObject<{
    type: z.ZodEnum<["code_change", "dependency_update", "config_change", "test_update", "documentation_update", "refactor", "type_annotation", "validation_update"]>;
    description: z.ZodString;
    confidence: z.ZodNumber;
    riskLevel: z.ZodNumber;
    estimatedEffort: z.ZodEnum<["low", "medium", "high"]>;
    filePath: z.ZodOptional<z.ZodString>;
    codeChange: z.ZodOptional<z.ZodObject<{
        oldCode: z.ZodString;
        newCode: z.ZodString;
        startLine: z.ZodNumber;
        endLine: z.ZodNumber;
    }, "strip", z.ZodTypeAny, {
        startLine?: number;
        endLine?: number;
        oldCode?: string;
        newCode?: string;
    }, {
        startLine?: number;
        endLine?: number;
        oldCode?: string;
        newCode?: string;
    }>>;
    dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    prerequisites: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
}, "strip", z.ZodTypeAny, {
    type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
    dependencies?: string[];
    description?: string;
    estimatedEffort?: "low" | "medium" | "high";
    riskLevel?: number;
    confidence?: number;
    filePath?: string;
    codeChange?: {
        startLine?: number;
        endLine?: number;
        oldCode?: string;
        newCode?: string;
    };
    prerequisites?: string[];
}, {
    type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
    dependencies?: string[];
    description?: string;
    estimatedEffort?: "low" | "medium" | "high";
    riskLevel?: number;
    confidence?: number;
    filePath?: string;
    codeChange?: {
        startLine?: number;
        endLine?: number;
        oldCode?: string;
        newCode?: string;
    };
    prerequisites?: string[];
}>;
export type RepairAction = z.infer<typeof RepairActionSchema>;
export declare const FailureArtifactSchema: z.ZodObject<{
    id: z.ZodString;
    title: z.ZodString;
    description: z.ZodString;
    severity: z.ZodEnum<["critical", "major", "minor", "info"]>;
    category: z.ZodEnum<["contract_violation", "test_failure", "type_error", "runtime_error", "build_error", "lint_error", "security_violation", "performance_issue", "accessibility_violation", "dependency_issue"]>;
    location: z.ZodOptional<z.ZodObject<{
        filePath: z.ZodString;
        startLine: z.ZodNumber;
        endLine: z.ZodNumber;
        startColumn: z.ZodOptional<z.ZodNumber>;
        endColumn: z.ZodOptional<z.ZodNumber>;
        functionName: z.ZodOptional<z.ZodString>;
        className: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        filePath?: string;
        startLine?: number;
        endLine?: number;
        startColumn?: number;
        endColumn?: number;
        functionName?: string;
        className?: string;
    }, {
        filePath?: string;
        startLine?: number;
        endLine?: number;
        startColumn?: number;
        endColumn?: number;
        functionName?: string;
        className?: string;
    }>>;
    context: z.ZodObject<{
        environment: z.ZodDefault<z.ZodString>;
        nodeVersion: z.ZodOptional<z.ZodString>;
        timestamp: z.ZodString;
        phase: z.ZodOptional<z.ZodEnum<["intent", "formal", "test", "code", "verify", "operate"]>>;
        command: z.ZodOptional<z.ZodString>;
        workingDirectory: z.ZodOptional<z.ZodString>;
        gitCommit: z.ZodOptional<z.ZodString>;
        gitBranch: z.ZodOptional<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        environment?: string;
        timestamp?: string;
        command?: string;
        phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
        nodeVersion?: string;
        workingDirectory?: string;
        gitCommit?: string;
        gitBranch?: string;
    }, {
        environment?: string;
        timestamp?: string;
        command?: string;
        phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
        nodeVersion?: string;
        workingDirectory?: string;
        gitCommit?: string;
        gitBranch?: string;
    }>;
    evidence: z.ZodObject<{
        stackTrace: z.ZodOptional<z.ZodString>;
        errorMessage: z.ZodOptional<z.ZodString>;
        errorType: z.ZodOptional<z.ZodString>;
        logs: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        metrics: z.ZodDefault<z.ZodRecord<z.ZodString, z.ZodNumber>>;
        sourceCode: z.ZodOptional<z.ZodString>;
        testOutput: z.ZodOptional<z.ZodString>;
        buildOutput: z.ZodOptional<z.ZodString>;
        lintOutput: z.ZodOptional<z.ZodString>;
        dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        relatedFiles: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        dependencies?: string[];
        metrics?: Record<string, number>;
        logs?: string[];
        sourceCode?: string;
        stackTrace?: string;
        errorMessage?: string;
        errorType?: string;
        testOutput?: string;
        buildOutput?: string;
        lintOutput?: string;
        relatedFiles?: string[];
    }, {
        dependencies?: string[];
        metrics?: Record<string, number>;
        logs?: string[];
        sourceCode?: string;
        stackTrace?: string;
        errorMessage?: string;
        errorType?: string;
        testOutput?: string;
        buildOutput?: string;
        lintOutput?: string;
        relatedFiles?: string[];
    }>;
    rootCause: z.ZodOptional<z.ZodObject<{
        primaryCause: z.ZodString;
        contributingFactors: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        confidence: z.ZodNumber;
        reasoning: z.ZodString;
        suggestedActions: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        confidence?: number;
        primaryCause?: string;
        contributingFactors?: string[];
        reasoning?: string;
        suggestedActions?: string[];
    }, {
        confidence?: number;
        primaryCause?: string;
        contributingFactors?: string[];
        reasoning?: string;
        suggestedActions?: string[];
    }>>;
    suggestedActions: z.ZodDefault<z.ZodArray<z.ZodObject<{
        type: z.ZodEnum<["code_change", "dependency_update", "config_change", "test_update", "documentation_update", "refactor", "type_annotation", "validation_update"]>;
        description: z.ZodString;
        confidence: z.ZodNumber;
        riskLevel: z.ZodNumber;
        estimatedEffort: z.ZodEnum<["low", "medium", "high"]>;
        filePath: z.ZodOptional<z.ZodString>;
        codeChange: z.ZodOptional<z.ZodObject<{
            oldCode: z.ZodString;
            newCode: z.ZodString;
            startLine: z.ZodNumber;
            endLine: z.ZodNumber;
        }, "strip", z.ZodTypeAny, {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        }, {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        }>>;
        dependencies: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        prerequisites: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    }, "strip", z.ZodTypeAny, {
        type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
        dependencies?: string[];
        description?: string;
        estimatedEffort?: "low" | "medium" | "high";
        riskLevel?: number;
        confidence?: number;
        filePath?: string;
        codeChange?: {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        };
        prerequisites?: string[];
    }, {
        type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
        dependencies?: string[];
        description?: string;
        estimatedEffort?: "low" | "medium" | "high";
        riskLevel?: number;
        confidence?: number;
        filePath?: string;
        codeChange?: {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        };
        prerequisites?: string[];
    }>, "many">>;
    relatedArtifacts: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
    metadata: z.ZodObject<{
        createdAt: z.ZodString;
        updatedAt: z.ZodString;
        version: z.ZodDefault<z.ZodString>;
        tags: z.ZodDefault<z.ZodArray<z.ZodString, "many">>;
        environment: z.ZodOptional<z.ZodRecord<z.ZodString, z.ZodString>>;
        source: z.ZodDefault<z.ZodString>;
    }, "strip", z.ZodTypeAny, {
        createdAt?: string;
        version?: string;
        environment?: Record<string, string>;
        source?: string;
        updatedAt?: string;
        tags?: string[];
    }, {
        createdAt?: string;
        version?: string;
        environment?: Record<string, string>;
        source?: string;
        updatedAt?: string;
        tags?: string[];
    }>;
}, "strip", z.ZodTypeAny, {
    id?: string;
    location?: {
        filePath?: string;
        startLine?: number;
        endLine?: number;
        startColumn?: number;
        endColumn?: number;
        functionName?: string;
        className?: string;
    };
    severity?: "critical" | "major" | "minor" | "info";
    description?: string;
    category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "build_error" | "lint_error" | "security_violation" | "performance_issue" | "accessibility_violation" | "dependency_issue";
    metadata?: {
        createdAt?: string;
        version?: string;
        environment?: Record<string, string>;
        source?: string;
        updatedAt?: string;
        tags?: string[];
    };
    context?: {
        environment?: string;
        timestamp?: string;
        command?: string;
        phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
        nodeVersion?: string;
        workingDirectory?: string;
        gitCommit?: string;
        gitBranch?: string;
    };
    title?: string;
    suggestedActions?: {
        type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
        dependencies?: string[];
        description?: string;
        estimatedEffort?: "low" | "medium" | "high";
        riskLevel?: number;
        confidence?: number;
        filePath?: string;
        codeChange?: {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        };
        prerequisites?: string[];
    }[];
    evidence?: {
        dependencies?: string[];
        metrics?: Record<string, number>;
        logs?: string[];
        sourceCode?: string;
        stackTrace?: string;
        errorMessage?: string;
        errorType?: string;
        testOutput?: string;
        buildOutput?: string;
        lintOutput?: string;
        relatedFiles?: string[];
    };
    rootCause?: {
        confidence?: number;
        primaryCause?: string;
        contributingFactors?: string[];
        reasoning?: string;
        suggestedActions?: string[];
    };
    relatedArtifacts?: string[];
}, {
    id?: string;
    location?: {
        filePath?: string;
        startLine?: number;
        endLine?: number;
        startColumn?: number;
        endColumn?: number;
        functionName?: string;
        className?: string;
    };
    severity?: "critical" | "major" | "minor" | "info";
    description?: string;
    category?: "contract_violation" | "test_failure" | "type_error" | "runtime_error" | "build_error" | "lint_error" | "security_violation" | "performance_issue" | "accessibility_violation" | "dependency_issue";
    metadata?: {
        createdAt?: string;
        version?: string;
        environment?: Record<string, string>;
        source?: string;
        updatedAt?: string;
        tags?: string[];
    };
    context?: {
        environment?: string;
        timestamp?: string;
        command?: string;
        phase?: "code" | "test" | "verify" | "intent" | "formal" | "operate";
        nodeVersion?: string;
        workingDirectory?: string;
        gitCommit?: string;
        gitBranch?: string;
    };
    title?: string;
    suggestedActions?: {
        type?: "refactor" | "code_change" | "dependency_update" | "config_change" | "test_update" | "documentation_update" | "type_annotation" | "validation_update";
        dependencies?: string[];
        description?: string;
        estimatedEffort?: "low" | "medium" | "high";
        riskLevel?: number;
        confidence?: number;
        filePath?: string;
        codeChange?: {
            startLine?: number;
            endLine?: number;
            oldCode?: string;
            newCode?: string;
        };
        prerequisites?: string[];
    }[];
    evidence?: {
        dependencies?: string[];
        metrics?: Record<string, number>;
        logs?: string[];
        sourceCode?: string;
        stackTrace?: string;
        errorMessage?: string;
        errorType?: string;
        testOutput?: string;
        buildOutput?: string;
        lintOutput?: string;
        relatedFiles?: string[];
    };
    rootCause?: {
        confidence?: number;
        primaryCause?: string;
        contributingFactors?: string[];
        reasoning?: string;
        suggestedActions?: string[];
    };
    relatedArtifacts?: string[];
}>;
export type FailureArtifact = z.infer<typeof FailureArtifactSchema>;
export interface FixStrategy {
    name: string;
    category: FailureCategory;
    confidence: number;
    riskLevel: number;
    description: string;
    canApply: (failure: FailureArtifact) => Promise<boolean>;
    generateFix: (failure: FailureArtifact) => Promise<RepairAction[]>;
}
export interface AppliedFix {
    strategy: string;
    actions: RepairAction[];
    success: boolean;
    filesModified: string[];
    errors: string[];
    warnings: string[];
    type?: string;
    description?: string;
    targetFile?: string;
    confidence?: number;
    metadata: {
        timestamp: string;
        duration: number;
        confidence: number;
        riskLevel: number;
    };
}
export interface SkippedFix {
    strategy: string;
    reason: string;
    confidence?: number;
    riskLevel?: number;
    error?: string;
}
export interface AutoFixConfig {
    dryRun: boolean;
    confidenceThreshold: number;
    maxRiskLevel: number;
    enabledCategories: FailureCategory[];
    maxFixesPerRun: number;
    timeoutMs: number;
    backupFiles: boolean;
    generateReport: boolean;
}
export interface FixResult {
    appliedFixes: AppliedFix[];
    skippedFixes: SkippedFix[];
    summary: {
        totalFailures: number;
        fixesApplied: number;
        fixesSkipped: number;
        filesModified: number;
        success: boolean;
        errors: string[];
        warnings: string[];
    };
    recommendations: string[];
    reportPath?: string;
    success: boolean;
    appliedActions: AppliedFix[];
    generatedFiles: string[];
    backupFiles: string[];
    errors: string[];
    analysis?: string;
    proposedFixes?: RepairAction[];
    riskAssessment?: RiskAssessment;
}
export interface RiskAssessment {
    level: number;
    factors: string[];
    mitigation: string[];
    recommendation: 'proceed' | 'caution' | 'abort';
}
export interface AutoFixOptions {
    dryRun?: boolean;
    confidenceThreshold?: number;
    maxRiskLevel?: number;
    timeoutMs?: number;
    maxIterations?: number;
    outputDir?: string;
}
export interface FailurePattern {
    pattern: string;
    frequency: number;
    categories: FailureCategory[];
    commonLocations: CodeLocation[];
    suggestedStrategies: string[];
    confidence: number;
}
