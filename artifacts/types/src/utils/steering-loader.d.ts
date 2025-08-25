/**
 * SteeringLoader provides utilities for loading and managing steering documents
 */
export declare class SteeringLoader {
    private steeringPath;
    private cache;
    constructor(projectRoot?: string);
    /**
     * Load a specific steering document
     */
    loadDocument(documentName: string): Promise<string | null>;
    /**
     * Load all core steering documents
     */
    loadCoreDocuments(): Promise<Record<string, string>>;
    /**
     * Load custom steering documents (those starting with 'custom-')
     */
    loadCustomDocuments(): Promise<Record<string, string>>;
    /**
     * Load all steering documents (core + custom)
     */
    loadAllDocuments(): Promise<Record<string, string>>;
    /**
     * Get steering context as a formatted string for AI agents
     */
    getSteeringContext(): Promise<string>;
    /**
     * Check if steering documents exist
     */
    hasSteeringDocuments(): Promise<boolean>;
    /**
     * Initialize default steering documents if they don't exist
     */
    initializeDefaults(): Promise<void>;
    /**
     * Clear the document cache
     */
    clearCache(): void;
}
