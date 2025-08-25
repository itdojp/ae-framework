#!/usr/bin/env node
import { Command } from 'commander';
/**
 * SBOM (Software Bill of Materials) CLI
 * Provides command-line interface for SBOM generation and management
 */
export declare class SBOMCLI {
    /**
     * Generate SBOM for project
     */
    generateSBOM(options: {
        projectRoot?: string;
        output?: string;
        format?: 'json' | 'xml';
        includeDevDeps?: boolean;
        includeVulns?: boolean;
        verbose?: boolean;
    }): Promise<void>;
    /**
     * Validate existing SBOM
     */
    validateSBOM(sbomPath: string, options: {
        verbose?: boolean;
    }): Promise<void>;
    /**
     * Compare two SBOMs
     */
    compareSBOMs(sbom1Path: string, sbom2Path: string, options: {
        verbose?: boolean;
    }): Promise<void>;
    /**
     * Generate CI/CD integration scripts
     */
    generateCIIntegration(options: {
        ciProvider?: 'github' | 'gitlab' | 'azure' | 'jenkins';
        output?: string;
        verbose?: boolean;
    }): Promise<void>;
    /**
     * Generate GitHub Actions workflow
     */
    private generateGitHubWorkflow;
    /**
     * Generate GitLab CI pipeline
     */
    private generateGitLabPipeline;
    /**
     * Generate Azure DevOps pipeline
     */
    private generateAzurePipeline;
    /**
     * Generate Jenkinsfile
     */
    private generateJenkinsfile;
}
/**
 * Create SBOM command for CLI
 */
export declare function createSBOMCommand(): Command;
