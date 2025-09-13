/**
 * Evidence Validator for ae-framework
 * Validates AI suggestions with evidence from documentation and code
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import { execSync } from 'child_process';

export interface ValidationResult {
  isValid: boolean;
  evidence: Evidence[];
  confidence: number;
  suggestions?: string[];
}

export interface Evidence {
  type: 'documentation' | 'code' | 'test' | 'standard' | 'pattern';
  source: string;
  content: string;
  relevance: number;
  location?: {
    file?: string;
    line?: number;
    url?: string;
  };
}

export interface ValidationOptions {
  requireDocumentation?: boolean;
  requireTests?: boolean;
  minConfidence?: number;
  searchDepth?: number;
  includeExternalDocs?: boolean;
}

export class EvidenceValidator {
  private documentationCache: Map<string, string> = new Map();
  private patternDatabase: Map<string, Pattern> = new Map();
  private readonly DEFAULT_MIN_CONFIDENCE = 0.6;

  constructor() {
    this.initializePatternDatabase();
  }

  /**
   * Validate a claim or suggestion with evidence
   */
  async validateClaim(
    claim: string,
    context: string,
    options: ValidationOptions = {}
  ): Promise<ValidationResult> {
    const {
      requireDocumentation = false,
      requireTests = false,
      minConfidence = this.DEFAULT_MIN_CONFIDENCE,
      searchDepth = 3,
      includeExternalDocs = true
    } = options;

    const evidence: Evidence[] = [];

    // Search for documentation evidence
    if (requireDocumentation || includeExternalDocs) {
      const docEvidence = await this.searchOfficialDocs(claim, context);
      evidence.push(...docEvidence);
    }

    // Search for code evidence
    const codeEvidence = await this.findCodeEvidence(claim, context, searchDepth);
    evidence.push(...codeEvidence);

    // Search for test evidence
    if (requireTests) {
      const testEvidence = await this.checkTestResults(claim, context);
      evidence.push(...testEvidence);
    }

    // Check against known patterns
    const patternEvidence = this.checkPatterns(claim, context);
    evidence.push(...patternEvidence);

    // Check coding standards
    const standardEvidence = await this.checkStandards(claim, context);
    evidence.push(...standardEvidence);

    // Calculate confidence score
    const confidence = this.calculateConfidence(evidence);

    // Generate suggestions if confidence is low
    let suggestions: string[] | undefined;
    if (confidence < minConfidence) {
      suggestions = this.generateSuggestions(claim, evidence);
    }

    const base = {
      isValid: confidence >= minConfidence && this.meetsRequirements(evidence, options),
      evidence: this.sortEvidenceByRelevance(evidence),
      confidence
    } as ValidationResult;
    return suggestions ? { ...base, suggestions } : base;
  }

  /**
   * Validate code implementation against specifications
   */
  async validateImplementation(
    code: string,
    specification: string
  ): Promise<ValidationResult> {
    const evidence: Evidence[] = [];

    // Check if code matches specification
    const specMatches = this.matchSpecification(code, specification);
    evidence.push(...specMatches);

    // Check for required patterns
    const patternMatches = this.validatePatterns(code, specification);
    evidence.push(...patternMatches);

    // Check for anti-patterns
    const antiPatterns = this.detectAntiPatterns(code);
    if (antiPatterns.length > 0) {
      evidence.push(...antiPatterns);
    }

    const confidence = this.calculateConfidence(evidence);

    const base: ValidationResult = {
      isValid: confidence >= 0.7 && antiPatterns.length === 0,
      evidence,
      confidence
    };
    if (antiPatterns.length > 0) {
      return {
        ...base,
        suggestions: ['Fix detected anti-patterns', ...antiPatterns.map(e => e.content)]
      };
    }
    return base;
  }

  /**
   * Search official documentation for evidence
   */
  private async searchOfficialDocs(claim: string, context: string): Promise<Evidence[]> {
    const evidence: Evidence[] = [];
    const keywords = this.extractKeywords(claim);

    // Search in local documentation
    const localDocs = await this.searchLocalDocs(keywords);
    evidence.push(...localDocs);

    // Search in package documentation
    const packageDocs = await this.searchPackageDocs(keywords, context);
    evidence.push(...packageDocs);

    // Search in online documentation (mock implementation)
    if (keywords.some(k => k.toLowerCase().includes('react'))) {
      evidence.push({
        type: 'documentation',
        source: 'React Official Docs',
        content: 'React component lifecycle and hooks documentation',
        relevance: 0.8,
        location: { url: 'https://react.dev/reference' }
      });
    }

    if (keywords.some(k => k.toLowerCase().includes('typescript'))) {
      evidence.push({
        type: 'documentation',
        source: 'TypeScript Handbook',
        content: 'TypeScript type system and best practices',
        relevance: 0.8,
        location: { url: 'https://www.typescriptlang.org/docs/' }
      });
    }

    return evidence;
  }

  /**
   * Find evidence in codebase
   */
  private async findCodeEvidence(
    claim: string,
    context: string,
    searchDepth: number
  ): Promise<Evidence[]> {
    const evidence: Evidence[] = [];
    const keywords = this.extractKeywords(claim);

    try {
      // Search for similar patterns in codebase
      for (const keyword of keywords) {
        const searchResults = await this.searchCodebase(keyword, searchDepth);
        evidence.push(...searchResults);
      }

      // Search for imports and usage
      const usageEvidence = await this.findUsagePatterns(keywords, context);
      evidence.push(...usageEvidence);
    } catch (error) {
      // Codebase search failed
    }

    return evidence;
  }

  /**
   * Check test results for evidence
   */
  private async checkTestResults(claim: string, context: string): Promise<Evidence[]> {
    const evidence: Evidence[] = [];

    try {
      // Check if tests exist for the claim
      const testFiles = await this.findTestFiles(context);
      
      for (const testFile of testFiles) {
        const content = await fs.readFile(testFile, 'utf-8');
        const relevantTests = this.extractRelevantTests(content, claim);
        
        if (relevantTests.length > 0) {
          evidence.push({
            type: 'test',
            source: path.basename(testFile),
            content: `Found ${relevantTests.length} relevant tests`,
            relevance: 0.9,
            location: { file: testFile }
          });
        }
      }

      // Try to run tests and check results
      const testResults = await this.runTests(testFiles);
      if (testResults.passed) {
        evidence.push({
          type: 'test',
          source: 'Test Execution',
          content: 'All relevant tests passed',
          relevance: 1.0
        });
      }
    } catch (error) {
      // Test checking failed
    }

    return evidence;
  }

  /**
   * Check against known patterns
   */
  private checkPatterns(claim: string, context: string): Evidence[] {
    const evidence: Evidence[] = [];
    const claimLower = claim.toLowerCase();

    for (const [patternName, pattern] of Array.from(this.patternDatabase)) {
      if (this.matchesPattern(claimLower, pattern)) {
        evidence.push({
          type: 'pattern',
          source: patternName,
          content: pattern.description,
          relevance: pattern.confidence,
          ...(pattern.reference ? { location: { url: pattern.reference } } : {})
        });
      }
    }

    return evidence;
  }

  /**
   * Check against coding standards
   */
  private async checkStandards(claim: string, context: string): Promise<Evidence[]> {
    const evidence: Evidence[] = [];

    try {
      // Check project coding standards
      const standardsFile = await this.findStandardsFile();
      if (standardsFile) {
        const standards = await fs.readFile(standardsFile, 'utf-8');
        const relevantStandards = this.extractRelevantStandards(standards, claim);
        
        for (const standard of relevantStandards) {
          evidence.push({
            type: 'standard',
            source: 'Project Standards',
            content: standard,
            relevance: 0.85,
            location: { file: standardsFile }
          });
        }
      }

      // Check against common standards
      const commonStandards = this.checkCommonStandards(claim);
      evidence.push(...commonStandards);
    } catch (error) {
      // Standards checking failed
    }

    return evidence;
  }

  /**
   * Calculate confidence score based on evidence
   */
  private calculateConfidence(evidence: Evidence[]): number {
    if (evidence.length === 0) return 0;

    // Weight evidence by type
    const weights: Record<Evidence['type'], number> = {
      documentation: 0.3,
      code: 0.25,
      test: 0.25,
      standard: 0.15,
      pattern: 0.05
    };

    let totalWeight = 0;
    let weightedSum = 0;

    for (const e of evidence) {
      const weight = weights[e.type];
      totalWeight += weight;
      weightedSum += weight * e.relevance;
    }

    // Bonus for multiple evidence types
    const typeCount = new Set(evidence.map(e => e.type)).size;
    const diversityBonus = Math.min(0.2, typeCount * 0.05);

    return Math.min(1.0, (weightedSum / totalWeight) + diversityBonus);
  }

  /**
   * Check if evidence meets requirements
   */
  private meetsRequirements(evidence: Evidence[], options: ValidationOptions): boolean {
    if (options.requireDocumentation) {
      if (!evidence.some(e => e.type === 'documentation')) {
        return false;
      }
    }

    if (options.requireTests) {
      if (!evidence.some(e => e.type === 'test')) {
        return false;
      }
    }

    return true;
  }

  /**
   * Generate suggestions when confidence is low
   */
  private generateSuggestions(claim: string, evidence: Evidence[]): string[] {
    const suggestions: string[] = [];

    const hasDocumentation = evidence.some(e => e.type === 'documentation');
    const hasTests = evidence.some(e => e.type === 'test');
    const hasCode = evidence.some(e => e.type === 'code');

    if (!hasDocumentation) {
      suggestions.push('Consult official documentation for this feature');
    }

    if (!hasTests) {
      suggestions.push('Write tests to validate the implementation');
    }

    if (!hasCode) {
      suggestions.push('Search for existing implementations in the codebase');
    }

    if (evidence.length < 3) {
      suggestions.push('Gather more evidence before proceeding');
    }

    return suggestions;
  }

  /**
   * Sort evidence by relevance
   */
  private sortEvidenceByRelevance(evidence: Evidence[]): Evidence[] {
    return evidence.sort((a, b) => b.relevance - a.relevance);
  }

  /**
   * Extract keywords from claim
   */
  private extractKeywords(claim: string): string[] {
    // Remove common words
    const stopWords = new Set(['the', 'is', 'at', 'which', 'on', 'a', 'an', 'as', 'are', 'was', 'were', 'to', 'for', 'of', 'with', 'in']);
    
    return claim
      .toLowerCase()
      .split(/\s+/)
      .filter(word => word.length > 2 && !stopWords.has(word))
      .map(word => word.replace(/[^a-z0-9]/g, ''))
      .filter(word => word.length > 0);
  }

  /**
   * Search local documentation
   */
  private async searchLocalDocs(keywords: string[]): Promise<Evidence[]> {
    const evidence: Evidence[] = [];
    const docsDir = path.join(process.cwd(), 'docs');

    try {
      const files = await this.scanDirectory(docsDir, '.md');
      
      for (const file of files) {
        const content = await fs.readFile(file, 'utf-8');
        const matches = this.findKeywordMatches(content, keywords);
        
        if (matches.length > 0) {
          evidence.push({
            type: 'documentation',
            source: path.basename(file),
            content: matches.join('; '),
            relevance: Math.min(1.0, matches.length * 0.2),
            location: { file }
          });
        }
      }
    } catch (error) {
      // Docs directory doesn't exist
    }

    return evidence;
  }

  /**
   * Search package documentation
   */
  private async searchPackageDocs(keywords: string[], context: string): Promise<Evidence[]> {
    const evidence: Evidence[] = [];

    try {
      // Check README
      const readme = await fs.readFile('README.md', 'utf-8');
      const matches = this.findKeywordMatches(readme, keywords);
      
      if (matches.length > 0) {
        evidence.push({
          type: 'documentation',
          source: 'README.md',
          content: matches.slice(0, 3).join('; '),
          relevance: 0.7,
          location: { file: 'README.md' }
        });
      }
    } catch (error) {
      // README doesn't exist
    }

    return evidence;
  }

  /**
   * Search codebase for patterns
   */
  private async searchCodebase(keyword: string, depth: number): Promise<Evidence[]> {
    const evidence: Evidence[] = [];

    try {
      // Use grep to search for keyword
      const result = execSync(
        `grep -r "${keyword}" --include="*.ts" --include="*.js" --exclude-dir=node_modules --exclude-dir=.git --exclude-dir=dist -m 5 .`,
        { encoding: 'utf-8', stdio: 'pipe', timeout: 1500, maxBuffer: 256 * 1024 }
      );

      const lines = result.split('\n').slice(0, depth);
      for (const line of lines) {
        if (line) {
          const [file, ...content] = line.split(':');
          if (file) {
            evidence.push({
              type: 'code',
              source: path.basename(file),
              content: content.join(':').trim(),
              relevance: 0.6,
              location: { file }
            });
          }
        }
      }
    } catch (error) {
      // Grep failed or no matches
    }

    return evidence;
  }

  /**
   * Find usage patterns in code
   */
  private async findUsagePatterns(keywords: string[], context: string): Promise<Evidence[]> {
    const evidence: Evidence[] = [];

    // Look for import statements
    for (const keyword of keywords) {
      try {
        const imports = execSync(
          `grep -r "import.*${keyword}" --include="*.ts" --include="*.js" --exclude-dir=node_modules --exclude-dir=.git --exclude-dir=dist .`,
          { encoding: 'utf-8', stdio: 'pipe', timeout: 1500, maxBuffer: 256 * 1024 }
        );

        if (imports) {
          evidence.push({
            type: 'code',
            source: 'Import Usage',
            content: `Found imports for ${keyword}`,
            relevance: 0.7
          });
        }
      } catch (error) {
        // No imports found
      }
    }

    return evidence;
  }

  /**
   * Find test files
   */
  private async findTestFiles(context: string): Promise<string[]> {
    const testFiles: string[] = [];
    const testDir = path.join(process.cwd(), 'tests');

    try {
      const files = await this.scanDirectory(testDir, '.test.ts');
      testFiles.push(...files);
    } catch (error) {
      // Test directory doesn't exist
    }

    return testFiles;
  }

  /**
   * Extract relevant tests from test file
   */
  private extractRelevantTests(content: string, claim: string): string[] {
    const tests: string[] = [];
    const keywords = this.extractKeywords(claim);
    const lines = content.split('\n');

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (line?.includes('test(') || line?.includes('it(')) {
        for (const keyword of keywords) {
          if (line?.toLowerCase().includes(keyword)) {
            tests.push(line.trim());
            break;
          }
        }
      }
    }

    return tests;
  }

  /**
   * Run tests and get results
   */
  private async runTests(testFiles: string[]): Promise<{ passed: boolean }> {
    // テスト環境では重い全体テスト実行を避ける。明示的に許可されたときのみ実行。
    if (process.env['EVIDENCE_RUN_TESTS'] !== '1') {
      return { passed: false };
    }
    try {
      execSync('npm test', { stdio: 'pipe', timeout: 5000, maxBuffer: 256 * 1024 });
      return { passed: true };
    } catch (error) {
      return { passed: false };
    }
  }

  /**
   * Find project standards file
   */
  private async findStandardsFile(): Promise<string | null> {
    const possibleFiles = [
      '.ae/steering/standards.md',
      'docs/standards.md',
      'CONTRIBUTING.md',
      '.eslintrc.json'
    ];

    for (const file of possibleFiles) {
      try {
        await fs.access(path.join(process.cwd(), file));
        return file;
      } catch (error) {
        // File doesn't exist
      }
    }

    return null;
  }

  /**
   * Extract relevant standards
   */
  private extractRelevantStandards(standards: string, claim: string): string[] {
    const relevant: string[] = [];
    const keywords = this.extractKeywords(claim);
    const lines = standards.split('\n');

    for (const line of lines) {
      for (const keyword of keywords) {
        if (line.toLowerCase().includes(keyword)) {
          relevant.push(line.trim());
          break;
        }
      }
    }

    return relevant;
  }

  /**
   * Check against common coding standards
   */
  private checkCommonStandards(claim: string): Evidence[] {
    const evidence: Evidence[] = [];
    const claimLower = claim.toLowerCase();

    const commonStandards = [
      { pattern: 'camelcase', standard: 'Use camelCase for function names' },
      { pattern: 'pascalcase', standard: 'Use PascalCase for class names' },
      { pattern: 'const', standard: 'Use const for immutable values' },
      { pattern: 'async', standard: 'Use async/await for asynchronous operations' },
      { pattern: 'error handling', standard: 'Always handle errors appropriately' }
    ];

    for (const { pattern, standard } of commonStandards) {
      if (claimLower.includes(pattern)) {
        evidence.push({
          type: 'standard',
          source: 'Common Standards',
          content: standard,
          relevance: 0.7
        });
      }
    }

    return evidence;
  }

  /**
   * Match code against specification
   */
  private matchSpecification(code: string, specification: string): Evidence[] {
    const evidence: Evidence[] = [];
    const specKeywords = this.extractKeywords(specification);

    let matchCount = 0;
    for (const keyword of specKeywords) {
      if (code.toLowerCase().includes(keyword)) {
        matchCount++;
      }
    }

    const matchRatio = matchCount / specKeywords.length;
    
    evidence.push({
      type: 'code',
      source: 'Specification Match',
      content: `Code matches ${Math.round(matchRatio * 100)}% of specification keywords`,
      relevance: matchRatio
    });

    return evidence;
  }

  /**
   * Validate against required patterns
   */
  private validatePatterns(code: string, specification: string): Evidence[] {
    const evidence: Evidence[] = [];

    // Check for required patterns based on specification
    if (specification.includes('class')) {
      if (code.includes('class ')) {
        evidence.push({
          type: 'pattern',
          source: 'Class Pattern',
          content: 'Required class pattern found',
          relevance: 0.9
        });
      }
    }

    if (specification.includes('async') || specification.includes('asynchronous')) {
      if (code.includes('async ') || code.includes('await ')) {
        evidence.push({
          type: 'pattern',
          source: 'Async Pattern',
          content: 'Required async pattern found',
          relevance: 0.9
        });
      }
    }

    return evidence;
  }

  /**
   * Detect anti-patterns in code
   */
  private detectAntiPatterns(code: string): Evidence[] {
    const antiPatterns: Evidence[] = [];

    // Check for common anti-patterns
    if (code.includes('var ')) {
      antiPatterns.push({
        type: 'pattern',
        source: 'Anti-pattern',
        content: 'Use of var instead of const/let',
        relevance: -0.5
      });
    }

    if (code.includes('== ') && !code.includes('=== ')) {
      antiPatterns.push({
        type: 'pattern',
        source: 'Anti-pattern',
        content: 'Use of == instead of ===',
        relevance: -0.3
      });
    }

    if (code.includes('eval(')) {
      antiPatterns.push({
        type: 'pattern',
        source: 'Anti-pattern',
        content: 'Use of eval() is dangerous',
        relevance: -0.9
      });
    }

    return antiPatterns;
  }

  /**
   * Check if claim matches a pattern
   */
  private matchesPattern(claim: string, pattern: Pattern): boolean {
    for (const keyword of pattern.keywords) {
      if (claim.includes(keyword)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Find keyword matches in content
   */
  private findKeywordMatches(content: string, keywords: string[]): string[] {
    const matches: string[] = [];
    const lines = content.split('\n');

    for (const line of lines) {
      for (const keyword of keywords) {
        if (line.toLowerCase().includes(keyword)) {
          matches.push(line.trim().substring(0, 100));
          break;
        }
      }
    }

    return matches;
  }

  /**
   * Scan directory for files
   */
  private async scanDirectory(dir: string, extension: string): Promise<string[]> {
    const files: string[] = [];

    try {
      const entries = await fs.readdir(dir, { withFileTypes: true });
      
      for (const entry of entries) {
        const fullPath = path.join(dir, entry.name);
        
        if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
          const subFiles = await this.scanDirectory(fullPath, extension);
          files.push(...subFiles);
        } else if (entry.isFile() && entry.name.endsWith(extension)) {
          files.push(fullPath);
        }
      }
    } catch (error) {
      // Directory doesn't exist or can't be read
    }

    return files;
  }

  /**
   * Initialize pattern database with common patterns
   */
  private initializePatternDatabase(): void {
    this.patternDatabase.set('singleton', {
      keywords: ['singleton', 'instance', 'getinstance'],
      description: 'Singleton pattern for single instance',
      confidence: 0.8,
      reference: 'https://refactoring.guru/design-patterns/singleton'
    });

    this.patternDatabase.set('factory', {
      keywords: ['factory', 'create', 'build'],
      description: 'Factory pattern for object creation',
      confidence: 0.8,
      reference: 'https://refactoring.guru/design-patterns/factory'
    });

    this.patternDatabase.set('observer', {
      keywords: ['observer', 'subscribe', 'listener', 'emit'],
      description: 'Observer pattern for event handling',
      confidence: 0.8,
      reference: 'https://refactoring.guru/design-patterns/observer'
    });

    this.patternDatabase.set('mvc', {
      keywords: ['model', 'view', 'controller', 'mvc'],
      description: 'Model-View-Controller architecture',
      confidence: 0.85
    });

    this.patternDatabase.set('restful', {
      keywords: ['rest', 'restful', 'get', 'post', 'put', 'delete'],
      description: 'RESTful API design pattern',
      confidence: 0.9
    });
  }

  /**
   * Validate a solution with evidence
   */
  async validateSolution(
    problem: string,
    solution: string,
    options: ValidationOptions = {}
  ): Promise<ValidationResult> {
    // First validate the solution claim
    const claimValidation = await this.validateClaim(solution, problem, options);

    // Then validate the implementation if provided
    if (solution.includes('```')) {
      // Extract code from markdown
      const codeMatch = solution.match(/```[\w]*\n([\s\S]*?)\n```/);
      if (codeMatch) {
        const code = codeMatch[1];
        const implValidation = await this.validateImplementation(code || '', problem);
        
        // Combine evidence
        const combinedEvidence = [...claimValidation.evidence, ...implValidation.evidence];
        const combinedConfidence = (claimValidation.confidence + implValidation.confidence) / 2;

        return {
          isValid: claimValidation.isValid && implValidation.isValid,
          evidence: this.sortEvidenceByRelevance(combinedEvidence),
          confidence: combinedConfidence,
          suggestions: [...(claimValidation.suggestions || []), ...(implValidation.suggestions || [])]
        };
      }
    }

    return claimValidation;
  }

  /**
   * Get evidence summary
   */
  getEvidenceSummary(evidence: Evidence[]): string {
    const byType = evidence.reduce((acc, e) => {
      if (!acc[e?.type || 'unknown']) acc[e?.type || 'unknown'] = [];
      acc[e?.type || 'unknown']?.push(e);
      return acc;
    }, {} as Record<string, Evidence[]>);

    let summary = 'Evidence Summary:\n';
    
    for (const [type, items] of Object.entries(byType)) {
      summary += `\n${type.toUpperCase()} (${items.length}):\n`;
      for (const item of items.slice(0, 3)) {
        summary += `  - ${item.source}: ${item.content.substring(0, 80)}...\n`;
      }
    }

    return summary;
  }
}

// Type definition for pattern
interface Pattern {
  keywords: string[];
  description: string;
  confidence: number;
  reference?: string;
}
