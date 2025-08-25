/**
 * Deterministic Code Generator
 * Ensures consistent code generation from AE-IR specifications
 */
export interface CodegenOptions {
    /** Input AE-IR file path */
    inputPath: string;
    /** Output directory for generated code */
    outputDir: string;
    /** Template directory */
    templateDir?: string;
    /** Target language/framework */
    target: 'typescript' | 'react' | 'api' | 'database';
    /** Enable drift detection */
    enableDriftDetection?: boolean;
    /** Custom hash algorithm */
    hashAlgorithm?: 'sha256' | 'md5';
    /** Preserve existing manual modifications */
    preserveManualChanges?: boolean;
}
export interface GeneratedFile {
    /** Relative file path */
    filePath: string;
    /** Generated content */
    content: string;
    /** Content hash for drift detection */
    hash: string;
    /** Generation timestamp */
    timestamp: string;
    /** Source specification hash */
    specHash: string;
}
export interface DriftDetectionResult {
    /** Whether drift was detected */
    hasDrift: boolean;
    /** Files with detected drift */
    driftedFiles: Array<{
        filePath: string;
        reason: 'spec_changed' | 'manual_modification' | 'template_changed';
        expectedHash: string;
        actualHash: string;
        lastGenerated: string;
    }>;
    /** Summary of drift analysis */
    summary: {
        totalFiles: number;
        driftedFiles: number;
        upToDateFiles: number;
    };
}
export interface CodegenManifest {
    /** Generation metadata */
    metadata: {
        generatedAt: string;
        specHash: string;
        templateHash: string;
        options: CodegenOptions;
    };
    /** Generated files registry */
    files: GeneratedFile[];
}
export declare class DeterministicCodeGenerator {
    private options;
    private manifestPath;
    constructor(options: CodegenOptions);
    /**
     * Generate code from AE-IR specification
     */
    generate(): Promise<CodegenManifest>;
    /**
     * Detect drift between current state and expected state
     */
    detectDrift(currentSpecHash: string): Promise<DriftDetectionResult>;
    /**
     * Generate files based on target and AE-IR
     */
    private generateFiles;
    /**
     * Generate TypeScript types and interfaces
     */
    private generateTypeScriptFiles;
    /**
     * Generate React components
     */
    private generateReactFiles;
    /**
     * Generate API handlers
     */
    private generateAPIFiles;
    /**
     * Generate database schemas
     */
    private generateDatabaseFiles;
    /**
     * Helper methods for code generation
     */
    private generateTypeScriptTypes;
    private generateAPIInterfaces;
    private generateValidationSchemas;
    private generateEntityForm;
    private generateEntityList;
    private generateAPIHandler;
    private generateSQLMigration;
    private generateORMModel;
    /**
     * Helper methods for type mapping
     */
    private mapTypeToTS;
    private mapTypeToZod;
    private mapTypeToInputType;
    private mapTypeToSQL;
    private getColumnOptions;
    /**
     * Utility methods
     */
    private loadAEIR;
    private loadManifest;
    private writeManifest;
    private calculateHash;
    private calculateTemplateHash;
}
