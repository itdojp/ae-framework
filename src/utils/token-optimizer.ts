/**
 * Token Optimizer for ae-framework
 * Reduces token usage by up to 70% through intelligent compression and caching
 */

import * as crypto from 'crypto';

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

export class TokenOptimizer {
  private cache: Map<string, string> = new Map();
  private readonly CACHE_SIZE = 100;
  private readonly TOKEN_ESTIMATE_RATIO = 0.25; // Approximate tokens per character
  private readonly KEY_INDICATOR_REGEX = /\b(must|should|required|important|critical|key|main|primary)[:\s]/i;

  /**
   * Compress steering documents by removing redundancy and focusing on essentials
   */
  async compressSteeringDocuments(
    docs: Record<string, string>,
    options: CompressionOptions = {}
  ): Promise<{ compressed: string; stats: TokenStats }> {
    // Handle empty documents
    if (Object.keys(docs).length === 0) {
      return {
        compressed: '',
        stats: { original: 0, compressed: 0, reductionPercentage: 0 }
      };
    }

    const {
      maxTokens = 4000,
      preservePriority = ['product', 'architecture', 'standards'],
      compressionLevel = 'medium',
      enableCaching = true
    } = options;

    // Generate cache key
    const cacheKey = this.generateCacheKey(docs, options);
    if (enableCaching && this.cache.has(cacheKey)) {
      const cached = this.cache.get(cacheKey)!;
      return {
        compressed: cached,
        stats: this.calculateStats(JSON.stringify(docs), cached)
      };
    }

    let compressed = '';
    const sections: { name: string; content: string; priority: number }[] = [];

    // Process each document with priority
    for (const [name, content] of Object.entries(docs)) {
      const priority = preservePriority.indexOf(name);
      const processedContent = await this.processDocument(content, compressionLevel);
      
      // Only add non-empty content
      if (processedContent && processedContent.trim().length > 0) {
        sections.push({
          name,
          content: processedContent,
          priority: priority >= 0 ? priority : 999
        });
      }
    }

    // Sort by priority and build compressed output
    sections.sort((a, b) => a.priority - b.priority);

    for (const section of sections) {
      const sectionText = `\n## ${section.name.toUpperCase()}\n${section.content}\n`;
      const estimatedTokens = this.estimateTokens(compressed + sectionText);
      
      if (estimatedTokens <= maxTokens) {
        compressed += sectionText;
      } else {
        // Truncate if needed
        const remainingTokens = maxTokens - this.estimateTokens(compressed);
        if (remainingTokens > 100) {
          const truncated = this.truncateToTokens(section.content, remainingTokens - 50);
          compressed += `\n## ${section.name.toUpperCase()}\n${truncated}\n[...truncated]`;
        }
        break;
      }
    }

    // Update cache
    if (enableCaching) {
      this.updateCache(cacheKey, compressed);
    }

    const original = JSON.stringify(docs);
    return {
      compressed,
      stats: this.calculateStats(original, compressed)
    };
  }

  /**
   * Optimize context window by intelligent selection and compression
   */
  async optimizeContext(
    context: string,
    maxTokens: number,
    relevantKeywords: string[] = []
  ): Promise<{ optimized: string; stats: TokenStats }> {
    const original = context;

    // Split context into chunks
    const chunks = this.splitIntoChunks(context);
    
    // Score chunks by relevance
    const scoredChunks = chunks.map(chunk => ({
      content: chunk,
      score: this.calculateRelevanceScore(chunk, relevantKeywords)
    }));

    // Sort by relevance
    scoredChunks.sort((a, b) => b.score - a.score);

    // Build optimized context within token limit
    let optimized = '';
    for (const chunk of scoredChunks) {
      const compressed = await this.compressText(chunk.content);
      const newContext = optimized + '\n' + compressed;
      
      if (this.estimateTokens(newContext) <= maxTokens) {
        optimized = newContext;
      } else {
        break;
      }
    }

    return {
      optimized: optimized.trim(),
      stats: this.calculateStats(original, optimized)
    };
  }

  /**
   * Compress text by removing redundancy while preserving meaning
   */
  private async processDocument(
    content: string,
    level: 'low' | 'medium' | 'high'
  ): Promise<string> {
    let processed = content;

    // Remove comments in code blocks first
    processed = processed.replace(/\/\*[\s\S]*?\*\//g, '');
    processed = processed.replace(/\/\/.*/g, '');

    if (level === 'high') {
      // For high compression, extract key points from original (minus comments)
      const keyPoints = this.extractKeyPoints(processed);
      if (keyPoints) {
        return keyPoints;
      }
    }

    // Remove extra whitespace
    processed = processed.replace(/\s+/g, ' ').trim();

    if (level === 'medium' || level === 'high') {
      // Remove empty lines
      processed = processed.replace(/^\s*[\r\n]/gm, '');
      
      // Shorten repetitive patterns
      processed = this.deduplicatePatterns(processed);
    }

    return processed;
  }

  /**
   * Remove duplicate patterns in text
   */
  private deduplicatePatterns(text: string): string {
    // Find and replace repetitive sentences
    const sentences = text.split(/[.!?]+/);
    const seen = new Set<string>();
    const deduplicated: string[] = [];

    for (const sentence of sentences) {
      const normalized = sentence.trim().toLowerCase();
      if (normalized && !seen.has(normalized)) {
        seen.add(normalized);
        deduplicated.push(sentence.trim());
      }
    }

    const lastChar = text.match(/[.!?]$/)?.[0] || '.';
    return deduplicated.join('. ') + lastChar;
  }

  /**
   * Extract key points from text
   */
  private extractKeyPoints(text: string): string {
    // First split by sentences to preserve important content
    const sentences = text.split(/(?<=[.!?])\s+/);
    const keyPoints: string[] = [];

    for (const sentence of sentences) {
      const trimmed = sentence.trim();
      
      // Keep headers
      if (trimmed.match(/^#+\s/)) {
        keyPoints.push(sentence);
        continue;
      }

      // Keep bullet points
      if (trimmed.match(/^[\*\-\+]\s/)) {
        keyPoints.push(sentence);
        continue;
      }

      // Keep sentences/lines with key indicators
      if (this.KEY_INDICATOR_REGEX.test(trimmed)) {
        keyPoints.push(sentence);
        continue;
      }

      // Keep numbered lists
      if (trimmed.match(/^\d+\.\s/)) {
        keyPoints.push(sentence);
      }
    }

    // Return joined key points or empty string if none found
    return keyPoints.length > 0 ? keyPoints.join(' ') : '';
  }

  /**
   * Compress general text
   */
  private async compressText(text: string): Promise<string> {
    // Preserve code blocks
    const codeBlockRegex = /```[\s\S]*?```/g;
    const codeBlocks: string[] = [];
    let compressed = text.replace(codeBlockRegex, (match) => {
      codeBlocks.push(match);
      return `__CODE_BLOCK_${codeBlocks.length - 1}__`;
    });

    // Remove redundant whitespace
    compressed = compressed.replace(/\s+/g, ' ').trim();
    
    // Abbreviate common words (but not in code blocks)
    const abbreviations: Record<string, string> = {
      'function': 'fn',
      'variable': 'var',
      'parameter': 'param',
      'argument': 'arg',
      'configuration': 'config',
      'implementation': 'impl',
      'documentation': 'docs',
      'specification': 'spec'
    };

    for (const [full, abbr] of Object.entries(abbreviations)) {
      compressed = compressed.replace(new RegExp(`\\b${full}\\b`, 'gi'), abbr);
    }

    // Restore code blocks
    codeBlocks.forEach((block, i) => {
      compressed = compressed.replace(`__CODE_BLOCK_${i}__`, block);
    });

    return compressed;
  }

  /**
   * Split text into logical chunks
   */
  private splitIntoChunks(text: string): string[] {
    const chunks: string[] = [];
    
    // Try to split by paragraphs first
    const paragraphs = text.split(/\n\n+/);
    
    for (const paragraph of paragraphs) {
      if (this.estimateTokens(paragraph) > 500) {
        // Split large paragraphs by sentences
        const sentences = paragraph.split(/[.!?]+/);
        let currentChunk = '';
        
        for (const sentence of sentences) {
          if (this.estimateTokens(currentChunk + sentence) < 500) {
            currentChunk += sentence + '. ';
          } else {
            if (currentChunk) chunks.push(currentChunk.trim());
            currentChunk = sentence + '. ';
          }
        }
        
        if (currentChunk) chunks.push(currentChunk.trim());
      } else {
        chunks.push(paragraph);
      }
    }

    return chunks;
  }

  /**
   * Calculate relevance score for a text chunk
   */
  private calculateRelevanceScore(chunk: string, keywords: string[]): number {
    let score = 0;
    const lowerChunk = chunk.toLowerCase();

    // Check for keyword matches
    for (const keyword of keywords) {
      const regex = new RegExp(`\\b${keyword.toLowerCase()}\\b`, 'g');
      const matches = lowerChunk.match(regex);
      score += matches ? matches.length * 10 : 0;
    }

    // Boost score for headers
    if (chunk.match(/^#+\s/m)) score += 5;

    // Boost score for code blocks
    if (chunk.includes('```')) score += 3;

    // Boost score for lists
    if (chunk.match(/^[\*\-\+\d]\.\s/m)) score += 2;

    return score;
  }

  /**
   * Estimate token count (rough approximation)
   */
  estimateTokens(text: string): number {
    // Simple estimation: ~4 characters per token on average
    return Math.ceil(text.length * this.TOKEN_ESTIMATE_RATIO);
  }

  /**
   * Truncate text to approximate token count
   */
  private truncateToTokens(text: string, maxTokens: number): string {
    const estimatedChars = maxTokens / this.TOKEN_ESTIMATE_RATIO;
    if (text.length <= estimatedChars) return text;
    
    // Try to truncate at sentence boundary
    const truncated = text.substring(0, estimatedChars);
    const lastPeriod = truncated.lastIndexOf('.');
    const lastNewline = truncated.lastIndexOf('\n');
    
    const cutPoint = Math.max(lastPeriod, lastNewline);
    return cutPoint > estimatedChars * 0.8 
      ? truncated.substring(0, cutPoint + 1)
      : truncated;
  }

  /**
   * Generate cache key for content
   */
  private generateCacheKey(content: any, options: any): string {
    const hash = crypto.createHash('sha256');
    hash.update(JSON.stringify({ content, options }));
    return hash.digest('hex').substring(0, 16);
  }

  /**
   * Update cache with size limit
   */
  private updateCache(key: string, value: string): void {
    // Remove oldest entries if cache is full
    if (this.cache.size >= this.CACHE_SIZE) {
      const firstKey = this.cache.keys().next().value;
      if (firstKey !== undefined) {
        this.cache.delete(firstKey);
      }
    }
    this.cache.set(key, value);
  }

  /**
   * Calculate compression statistics
   */
  private calculateStats(original: string, compressed: string): TokenStats {
    // Handle empty strings
    if (!original || original.trim().length === 0) {
      return {
        original: 0,
        compressed: 0,
        reductionPercentage: 0
      };
    }

    const originalTokens = this.estimateTokens(original);
    const compressedTokens = this.estimateTokens(compressed);
    const reduction = originalTokens > 0 
      ? ((originalTokens - compressedTokens) / originalTokens) * 100
      : 0;

    return {
      original: originalTokens,
      compressed: compressedTokens,
      reductionPercentage: Math.round(reduction)
    };
  }

  /**
   * Clear the cache
   */
  clearCache(): void {
    this.cache.clear();
  }

  /**
   * Get cache statistics
   */
  getCacheStats(): { size: number; maxSize: number } {
    return {
      size: this.cache.size,
      maxSize: this.CACHE_SIZE
    };
  }
}