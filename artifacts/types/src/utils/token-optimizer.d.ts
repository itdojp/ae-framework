/**
 * Token Optimizer for ae-framework
 * Reduces token usage by up to 70% through intelligent compression and caching
 */
export interface CompressionOptions {
    maxTokens?: number;
    preservePriority?: string[];
    compressionLevel?: 'low' | 'medium' | 'high';
    enableCaching?: boolean;
}
export interface TokenStats {
    original: number;
    compressed: number;
    reductionPercentage: number;
}
export declare class TokenOptimizer {
    private cache;
    private readonly CACHE_SIZE;
    private readonly TOKEN_ESTIMATE_RATIO;
    private readonly KEY_INDICATOR_REGEX;
    /**
     * Compress steering documents by removing redundancy and focusing on essentials
     */
    compressSteeringDocuments(docs: Record<string, string>, options?: CompressionOptions): Promise<{
        compressed: string;
        stats: TokenStats;
    }>;
    /**
     * Optimize context window by intelligent selection and compression
     */
    optimizeContext(context: string, maxTokens: number, relevantKeywords?: string[]): Promise<{
        optimized: string;
        stats: TokenStats;
    }>;
    /**
     * Compress text by removing redundancy while preserving meaning
     */
    private processDocument;
    /**
     * Remove duplicate patterns in text
     */
    private deduplicatePatterns;
    /**
     * Extract key points from text
     */
    private extractKeyPoints;
    /**
     * Compress general text
     */
    private compressText;
    /**
     * Split text into logical chunks
     */
    private splitIntoChunks;
    /**
     * Calculate relevance score for a text chunk
     */
    private calculateRelevanceScore;
    /**
     * Estimate token count (rough approximation)
     */
    estimateTokens(text: string): number;
    /**
     * Truncate text to approximate token count
     */
    private truncateToTokens;
    /**
     * Generate cache key for content
     */
    private generateCacheKey;
    /**
     * Update cache with size limit
     */
    private updateCache;
    /**
     * Calculate compression statistics
     */
    private calculateStats;
    /**
     * Clear the cache
     */
    clearCache(): void;
    /**
     * Get cache statistics
     */
    getCacheStats(): {
        size: number;
        maxSize: number;
    };
}
