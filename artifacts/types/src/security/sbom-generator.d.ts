/**
 * Software Bill of Materials (SBOM) Generator
 * Generates comprehensive SBOMs for security and compliance
 */
export interface SBOMComponent {
    name: string;
    version: string;
    type: 'library' | 'framework' | 'application' | 'container' | 'file' | 'operating-system';
    supplier?: string;
    author?: string;
    description?: string;
    licenses?: string[];
    cpe?: string;
    purl?: string;
    hashes?: {
        algorithm: string;
        value: string;
    }[];
    externalReferences?: {
        type: string;
        url: string;
    }[];
    dependencies?: string[];
    vulnerabilities?: {
        id: string;
        severity: 'low' | 'medium' | 'high' | 'critical';
        description?: string;
        references?: string[];
    }[];
}
export interface SBOMMetadata {
    timestamp: string;
    tools: {
        vendor: string;
        name: string;
        version: string;
    }[];
    authors: string[];
    supplier?: string;
}
export interface SBOM {
    bomFormat: string;
    specVersion: string;
    serialNumber: string;
    version: number;
    metadata: SBOMMetadata;
    components: SBOMComponent[];
    dependencies?: {
        ref: string;
        dependsOn?: string[];
    }[];
    vulnerabilities?: {
        bom_ref: string;
        id: string;
        source?: {
            name: string;
            url: string;
        };
        ratings?: {
            source?: string;
            score?: number;
            severity?: string;
            method?: string;
        }[];
        cwes?: number[];
        description?: string;
        advisories?: {
            title?: string;
            url?: string;
        }[];
    }[];
}
export interface SBOMGeneratorOptions {
    projectRoot: string;
    outputPath?: string;
    includeDevDependencies?: boolean;
    includeLicenses?: boolean;
    includeHashes?: boolean;
    includeVulnerabilities?: boolean;
    format?: 'json' | 'xml';
    customComponents?: SBOMComponent[];
}
export declare class SBOMGenerator {
    private options;
    constructor(options: SBOMGeneratorOptions);
    /**
     * Generate complete SBOM
     */
    generate(): Promise<SBOM>;
    /**
     * Generate and save SBOM to file
     */
    generateAndSave(): Promise<string>;
    /**
     * Extract package dependencies from package.json and package-lock.json
     */
    private extractPackageDependencies;
    /**
     * Extract application files
     */
    private extractApplicationFiles;
    /**
     * Generate metadata section
     */
    private generateMetadata;
    /**
     * Extract dependency graph
     */
    private extractDependencyGraph;
    /**
     * Extract vulnerabilities (placeholder for vulnerability scanning integration)
     */
    private extractVulnerabilities;
    /**
     * Extract license information
     */
    private extractLicenses;
    /**
     * Generate file hashes
     */
    private generateFileHashes;
    /**
     * Generate serial number for SBOM
     */
    private generateSerialNumber;
    /**
     * Convert SBOM to XML format (CycloneDX XML)
     */
    private convertToXML;
    /**
     * Simple hash function for deterministic mock data generation
     */
    private simpleHash;
    /**
     * Escape XML characters
     */
    private escapeXML;
}
