import * as fs from 'fs';
import * as path from 'path';

/**
 * SteeringLoader provides utilities for loading and managing steering documents
 */
export class SteeringLoader {
  private steeringPath: string;
  private cache: Map<string, string> = new Map();

  constructor(projectRoot?: string) {
    const root = projectRoot || process.cwd();
    this.steeringPath = path.join(root, '.ae', 'steering');
  }

  /**
   * Load a specific steering document
   */
  async loadDocument(documentName: string): Promise<string | null> {
    const cacheKey = documentName;
    
    // Check cache first
    if (this.cache.has(cacheKey)) {
      return this.cache.get(cacheKey)!;
    }

    const filePath = path.join(this.steeringPath, `${documentName}.md`);
    
    try {
      const content = await fs.promises.readFile(filePath, 'utf-8');
      this.cache.set(cacheKey, content);
      return content;
    } catch (error) {
      // Document doesn't exist or can't be read
      return null;
    }
  }

  /**
   * Load all core steering documents
   */
  async loadCoreDocuments(): Promise<Record<string, string>> {
    const coreDocuments = ['product', 'architecture', 'standards'];
    const documents: Record<string, string> = {};

    for (const doc of coreDocuments) {
      const content = await this.loadDocument(doc);
      if (content) {
        documents[doc] = content;
      }
    }

    return documents;
  }

  /**
   * Load custom steering documents (those starting with 'custom-')
   */
  async loadCustomDocuments(): Promise<Record<string, string>> {
    const documents: Record<string, string> = {};

    try {
      const files = await fs.promises.readdir(this.steeringPath);
      const customFiles = files.filter(f => f.startsWith('custom-') && f.endsWith('.md'));

      for (const file of customFiles) {
        const name = file.replace('.md', '');
        const content = await this.loadDocument(name);
        if (content) {
          documents[name] = content;
        }
      }
    } catch (error) {
      // Directory doesn't exist or can't be read
      return documents;
    }

    return documents;
  }

  /**
   * Load all steering documents (core + custom)
   */
  async loadAllDocuments(): Promise<Record<string, string>> {
    const core = await this.loadCoreDocuments();
    const custom = await this.loadCustomDocuments();
    
    return { ...core, ...custom };
  }

  /**
   * Get steering context as a formatted string for AI agents
   */
  async getSteeringContext(): Promise<string> {
    const documents = await this.loadAllDocuments();
    
    if (Object.keys(documents).length === 0) {
      return 'No steering documents found.';
    }

    let context = '# Project Steering Context\n\n';
    
    for (const [name, content] of Object.entries(documents)) {
      const title = name.replace('custom-', '').replace(/-/g, ' ')
        .split(' ')
        .map(word => word.charAt(0).toUpperCase() + word.slice(1))
        .join(' ');
      
      context += `## ${title} Document\n\n`;
      context += content;
      context += '\n\n---\n\n';
    }

    return context;
  }

  /**
   * Check if steering documents exist
   */
  async hasSteeringDocuments(): Promise<boolean> {
    try {
      const stats = await fs.promises.stat(this.steeringPath);
      if (!stats.isDirectory()) {
        return false;
      }

      const files = await fs.promises.readdir(this.steeringPath);
      return files.some(f => f.endsWith('.md'));
    } catch (error) {
      return false;
    }
  }

  /**
   * Initialize default steering documents if they don't exist
   */
  async initializeDefaults(): Promise<void> {
    try {
      // Create directory if it doesn't exist
      await fs.promises.mkdir(this.steeringPath, { recursive: true });

      // Check if core documents exist
      const coreDocuments = ['product', 'architecture', 'standards'];
      
      for (const doc of coreDocuments) {
        const filePath = path.join(this.steeringPath, `${doc}.md`);
        
        try {
          await fs.promises.access(filePath);
          // File exists, skip
        } catch {
          // File doesn't exist, create default
          // The default templates are already created separately
        }
      }
    } catch (error) {
      console.error('Failed to initialize steering documents:', error);
    }
  }

  /**
   * Clear the document cache
   */
  clearCache(): void {
    this.cache.clear();
  }
}