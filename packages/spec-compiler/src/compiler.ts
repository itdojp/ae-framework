import { readFileSync, writeFileSync } from 'fs';
import { v4 as uuidv4, v5 as uuidv5 } from 'uuid';
import type { AEIR, CompileOptions, SpecLintReport, SpecLintIssue } from './types.js';
import { StrictAEIRSchema, validateAEIR, createAEIRValidator } from './strict-schema.js';

const INVARIANT_NAMESPACE_UUID = 'f309bd85-aea8-4418-9215-6134f52d6800';

export class AESpecCompiler {
  /**
   * Compile AE-Spec markdown to AE-IR JSON
   */
  async compile(options: CompileOptions): Promise<AEIR> {
    const { inputPath, outputPath, validate = true } = options;
    
    try {
      const markdown = readFileSync(inputPath, 'utf-8');
      let ir = this.parseMarkdownToIR(markdown);
      // Lenient normalization: in relaxed mode, coerce certain fields for smoother iteration
      if (process.env['AE_SPEC_RELAXED'] === '1') {
        ir = this.applyLenientNormalizations(ir);
      }
      
      if (validate) {
        const lintResult = await this.lint(ir);
        if (!lintResult.passed) {
          throw new Error(`Validation failed: ${lintResult.issues.length} issues found`);
        }
      }
      
      if (outputPath) {
        writeFileSync(outputPath, JSON.stringify(ir, null, 2), 'utf-8');
      }
      
      return ir;
    } catch (error) {
      throw new Error(`Compilation failed: ${(error as Error).message}`);
    }
  }

  /**
   * Lint AE-IR for quality issues with strict schema validation
   */
  async lint(ir: AEIR): Promise<SpecLintReport> {
    const issues: SpecLintIssue[] = [];
    
    // Strict schema validation first
    this.validateStrictSchema(ir, issues);
    
    // Basic structure validation
    this.validateStructure(ir, issues);
    
    // Business logic validation
    this.validateBusinessLogic(ir, issues);
    
    // Consistency validation
    this.validateConsistency(ir, issues);
    
    // Completeness validation
    this.validateCompleteness(ir, issues);
    
    const summary = {
      errors: issues.filter(i => i.severity === 'error').length,
      warnings: issues.filter(i => i.severity === 'warn').length,
      infos: issues.filter(i => i.severity === 'info').length,
    };
    
    return {
      passed: summary.errors === 0,
      issues: issues.sort((a, b) => {
        const severityOrder = { error: 0, warn: 1, info: 2 };
        return severityOrder[a.severity] - severityOrder[b.severity];
      }),
      summary
    };
  }

  private parseMarkdownToIR(markdown: string): AEIR {
    const sections = this.extractSections(markdown);
    const timestamp = new Date().toISOString();
    const metadata: AEIR['metadata'] = {
      name: sections['title'] || 'Untitled Specification',
      created: timestamp,
      updated: timestamp,
    };
    if (sections['description']) {
      metadata.description = sections['description'];
    }
    const glossary = this.parseGlossary(sections['glossary'] || '');
    const domain = this.parseDomain(sections['domain'] || '');
    const invariantSectionContent = [
      sections['invariants'],
      sections['stateinvariants'],
      sections['businessrules'],
      sections['businesslogic'],
      sections['rules'],
    ]
      .filter((value): value is string => Boolean(value && value.trim()))
      .join('\n');
    const invariants = this.parseInvariants(invariantSectionContent, domain);
    const usecases = this.parseUsecases(sections['usecases'] || '');
    const api = this.parseAPI(sections['api'] || '');
    const st = this.parseStateMachines(sections['statemachines']);
    const ui = this.parseUI(sections['ui']);
    const nfr = this.parseNFR(sections['nfr']);
    const base = { version: '1.0.0', metadata, glossary, domain, invariants, usecases, api } as AEIR;
    if (st) (base as any).statemachines = st;
    if (ui) (base as any).ui = ui;
    if (nfr) (base as any).nfr = nfr;
    return base;
  }

  private extractSections(markdown: string): Record<string, string> {
    const sections: Record<string, string> = {};
    const lines = markdown.split('\n');
    let currentSection = '';
    let currentContent: string[] = [];
    
    for (const line of lines) {
      if (line.startsWith('# ')) {
        if (currentSection) {
          sections[currentSection] = currentContent.join('\n').trim();
        }
        sections['title'] = line.substring(2).trim();
        currentSection = 'description';
        currentContent = [];
      } else if (line.startsWith('## ')) {
        if (currentSection) {
          sections[currentSection] = currentContent.join('\n').trim();
        }
        currentSection = line.substring(3).trim().toLowerCase().replace(/\s+/g, '');
        currentContent = [];
      } else {
        currentContent.push(line);
      }
    }
    
    if (currentSection) {
      sections[currentSection] = currentContent.join('\n').trim();
    }
    
    return sections;
  }

  private parseGlossary(content: string): AEIR['glossary'] {
    const glossary: AEIR['glossary'] = [];
    const lines = content.split('\n');
    
    for (const line of lines) {
      const match = line.match(/^[-*]\s*\*\*(.+?)\*\*:\s*(.+)$/);
      if (match && match[1] && match[2]) {
        glossary.push({
          term: match[1].trim(),
          definition: match[2].trim(),
        });
      }
    }
    
    return glossary;
  }

  private parseDomain(content: string): AEIR['domain'] {
    const entities: AEIR['domain'] = [];
    const lines = content.split('\n');
    let currentEntity: any = null;
    
    for (const line of lines) {
      const entityMatch = line.match(/^###\s+(.+)$/);
      if (entityMatch) {
        if (currentEntity) {
          entities.push(currentEntity);
        }
        currentEntity = {
          name: entityMatch[1]?.trim() || 'UnknownEntity',
          fields: [],
        };
      } else if (currentEntity) {
        const fieldMatch = line.match(/^[-*]\s*\*\*(.+?)\*\*\s*\((.+?)\)(?:\s*-\s*(.+))?$/);
        if (fieldMatch && fieldMatch[1] && fieldMatch[2]) {
          const typeRaw = fieldMatch[2].trim();
          const typeParts = typeRaw.split(',').map(s => s.trim());
          const required = typeParts.includes('required');
          const type = typeParts.filter(part => part !== 'required').join(', ');
          
          currentEntity.fields.push({
            name: fieldMatch[1].trim(),
            type: type || typeRaw,
            required,
            description: fieldMatch[3]?.trim(),
          });
        }
      }
    }
    
    if (currentEntity) {
      entities.push(currentEntity);
    }
    
    return entities;
  }

  private parseInvariants(content: string, domain: AEIR['domain'] = []): AEIR['invariants'] {
    const invariants: AEIR['invariants'] = [];
    const lines = content.split('\n');
    let counter = 0;
    
    for (const line of lines) {
      const raw = this.extractInvariantRawText(line);
      if (!raw) continue;
      const description = this.normalizeInvariantText(raw);
      if (!description) continue;
      const entities = this.extractInvariantEntities(raw, description, domain);
      if (entities.length === 0) continue;
      counter += 1;

      invariants.push({
        id: uuidv5(`${counter}:${description}`, INVARIANT_NAMESPACE_UUID),
        description,
        expression: description, // In real implementation, parse to formal expression
        entities,
        severity: 'error',
      });
    }
    
    return invariants;
  }

  private extractInvariantRawText(line: string): string | null {
    const trimmed = line.trim();
    if (!trimmed) return null;

    const bulletMatch = trimmed.match(/^[-*]\s+(.+)$/u);
    if (bulletMatch?.[1]) {
      return bulletMatch[1].trim();
    }

    const orderedMatch = trimmed.match(/^\d+[.)]\s+(.+)$/u);
    if (orderedMatch?.[1]) {
      return orderedMatch[1].trim();
    }

    return null;
  }

  private normalizeInvariantText(value: string): string {
    return value
      .trim()
      .replace(/^\*\*([^*]+)\*\*:\s*/u, '')
      .replace(/^`([^`]+)`:\s*/u, '')
      .replace(/^(?:BR|INV)-[A-Z0-9_-]+:\s*/iu, '')
      .replace(/\s+/gu, ' ')
      .trim();
  }

  private extractInvariantEntities(rawLine: string, description: string, domain: AEIR['domain']): string[] {
    if (!Array.isArray(domain) || domain.length === 0) {
      return [];
    }

    const matched = new Set<string>();
    this.findEntityMatchesInText(description, domain).forEach((name) => matched.add(name));
    this.findEntityMatchesByRuleTag(rawLine, domain).forEach((name) => matched.add(name));

    if (matched.size === 0 && domain.length === 1 && domain[0]?.name) {
      matched.add(domain[0].name);
    }

    return [...matched];
  }

  private findEntityMatchesInText(text: string, domain: AEIR['domain']): string[] {
    const matches = new Set<string>();
    const loweredText = text.toLowerCase();
    const fieldTermOwners = new Map<string, Set<string>>();

    for (const entity of domain) {
      for (const field of entity.fields || []) {
        for (const term of this.buildFieldSearchTerms(field.name)) {
          if (!fieldTermOwners.has(term)) {
            fieldTermOwners.set(term, new Set<string>());
          }
          fieldTermOwners.get(term)?.add(entity.name);
        }
      }
    }

    for (const entity of domain) {
      const nameTerms = this.buildEntitySearchTerms(entity.name);
      if (nameTerms.some((term) => this.containsSearchTerm(loweredText, term))) {
        matches.add(entity.name);
        continue;
      }

      const fieldTerms = (entity.fields || [])
        .flatMap((field) => this.buildFieldSearchTerms(field.name))
        .filter((term) => {
          const owners = fieldTermOwners.get(term);
          return owners?.size === 1 && owners.has(entity.name);
        });
      if (fieldTerms.some((term) => this.containsSearchTerm(loweredText, term))) {
        matches.add(entity.name);
      }
    }

    return [...matches];
  }

  private findEntityMatchesByRuleTag(rawLine: string, domain: AEIR['domain']): string[] {
    const matches = new Set<string>();
    const tags = [...rawLine.matchAll(/\b(?:BR|INV)-([A-Z0-9_]+)/gu)]
      .map((match) => match[1]?.toLowerCase().replace(/[^a-z0-9]/gu, '') || '')
      .filter(Boolean);

    if (tags.length === 0) return [];

    for (const entity of domain) {
      const entityKey = this.splitIdentifierTokens(entity.name).join('');
      for (const tag of tags) {
        if (
          tag === entityKey
          || (tag.length >= 4 && entityKey.includes(tag))
          || (entityKey.length >= 4 && tag.includes(entityKey))
        ) {
          matches.add(entity.name);
        }
      }
    }

    return [...matches];
  }

  private buildEntitySearchTerms(name: string): string[] {
    const tokens = this.splitIdentifierTokens(name);
    if (tokens.length === 0) return [];

    const terms = new Set<string>();
    const spaced = tokens.join(' ');
    const compact = tokens.join('');
    terms.add(name.trim().toLowerCase());
    terms.add(spaced);
    terms.add(compact);

    const pluralTokens = [...tokens];
    pluralTokens[pluralTokens.length - 1] = this.pluralizeToken(pluralTokens[pluralTokens.length - 1] || '');
    terms.add(pluralTokens.join(' '));
    terms.add(pluralTokens.join(''));

    return [...terms].filter((term) => term.length >= 2);
  }

  private buildFieldSearchTerms(fieldName: string): string[] {
    const ignored = new Set([
      'id',
      'name',
      'type',
      'state',
      'status',
      'createdat',
      'updatedat',
    ]);
    const tokens = this.splitIdentifierTokens(fieldName);
    if (tokens.length === 0) return [];

    const terms = new Set<string>();
    const spaced = tokens.join(' ');
    const compact = tokens.join('');
    terms.add(spaced);
    terms.add(compact);

    if (tokens.length > 1) {
      terms.add(tokens[tokens.length - 1] || '');
    }

    return [...terms].filter((term) => {
      const normalized = term.replace(/[^a-z0-9]/gu, '');
      return normalized.length >= 3 && !ignored.has(normalized);
    });
  }

  private splitIdentifierTokens(value: string): string[] {
    return value
      .replace(/([a-z0-9])([A-Z])/gu, '$1 $2')
      .replace(/[_-]+/gu, ' ')
      .trim()
      .toLowerCase()
      .split(/[^a-z0-9]+/gu)
      .filter(Boolean);
  }

  private pluralizeToken(token: string): string {
    if (!token) return token;
    if (token.endsWith('ies') || token.endsWith('ses') || token.endsWith('s')) return token;
    if (token.endsWith('y') && token.length > 1) return `${token.slice(0, -1)}ies`;
    if (token.endsWith('x') || token.endsWith('ch') || token.endsWith('sh')) return `${token}es`;
    return `${token}s`;
  }

  private containsSearchTerm(text: string, term: string): boolean {
    const normalized = term.trim().toLowerCase();
    if (!normalized) return false;
    const escaped = this.escapeRegExp(normalized).replace(/\s+/gu, '\\s+');
    const pattern = new RegExp(`(^|[^a-z0-9])${escaped}([^a-z0-9]|$)`, 'u');
    return pattern.test(text);
  }

  private escapeRegExp(value: string): string {
    return value.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&');
  }

  private parseUsecases(content: string): AEIR['usecases'] {
    const usecases: AEIR['usecases'] = [];
    const sections = content.split(/^###\s+/m);
    
    for (const section of sections.slice(1)) {
      const lines = section.split('\n');
      const name = lines[0]?.trim() || 'Unnamed Use Case';
      const usecase: NonNullable<AEIR['usecases']>[number] = {
        name,
        actor: 'User', // Extract from content
        steps: [],
      };
      
      let stepCounter = 1;
      for (const line of lines.slice(1)) {
        const stepMatch = line.match(/^[-*]\s*(.+)$/);
        if (stepMatch) {
          usecase.steps.push({
            step: stepCounter++,
            description: stepMatch?.[1]?.trim() || 'Step description',
            type: 'action', // Infer from content
          });
        }
      }
      
      if (usecase.steps.length > 0) {
        usecases.push(usecase);
      }
    }
    
    return usecases;
  }

  private parseStateMachines(content?: string): AEIR['statemachines'] {
    if (!content) return undefined;
    // Simplified state machine parsing - extend as needed
    return [];
  }

  private parseAPI(content: string): AEIR['api'] {
    const apis: AEIR['api'] = [];
    const lines = content.split('\n');
    
    for (const line of lines) {
      const match = line.match(/^[-*]\s*(GET|POST|PUT|PATCH|DELETE)\s+(.+?)(?:\s*-\s*(.+))?$/);
      if (match) {
        const base = {
          method: (match?.[1] as any) || 'GET',
          path: match?.[2]?.trim() || '/api',
        } as const;
        const withSummary = match?.[3] ? { summary: match[3].trim() } : {};
        apis.push({ ...base, ...withSummary });
      }
    }
    
    return apis;
  }

  private parseUI(content?: string): AEIR['ui'] {
    if (!content) return undefined;
    // Simplified UI parsing - extend as needed
    return {
      viewModels: [],
      pages: [],
    };
  }

  private parseNFR(content?: string): AEIR['nfr'] {
    if (!content) return undefined;
    // Simplified NFR parsing - extend as needed
    return {
      performance: {},
      security: {},
    };
  }

  private validateStructure(ir: AEIR, issues: SpecLintIssue[]): void {
    if (!ir.metadata?.name) {
      issues.push({
        id: 'STRUCT_001',
        severity: 'error',
        message: 'Specification must have a name in metadata',
        location: { section: 'metadata' },
      });
    }

    if (ir.domain.length === 0) {
      issues.push({
        id: 'STRUCT_002',
        severity: 'warn',
        message: 'No domain entities defined',
        location: { section: 'domain' },
      });
    }

    const apiCount = (ir.api ?? []).length;
    if (apiCount === 0) {
      issues.push({
        id: 'STRUCT_003',
        severity: 'info',
        message: 'No API endpoints defined',
        location: { section: 'api' },
      });
    }
  }

  private validateBusinessLogic(ir: AEIR, issues: SpecLintIssue[]): void {
    // Check for entities without any business rules
    const invariants = ir.invariants ?? [];
    const entitiesWithRules = new Set(invariants.flatMap(inv => inv.entities ?? []));
    
    for (const entity of ir.domain) {
      if (!entitiesWithRules.has(entity.name)) {
        issues.push({
          id: 'BIZ_001',
          severity: 'warn',
          message: `Entity '${entity.name}' has no business rules defined`,
          location: { section: 'domain' },
          suggestion: 'Consider adding invariants or constraints for this entity',
        });
      }
    }
  }

  private validateConsistency(ir: AEIR, issues: SpecLintIssue[]): void {
    const entityNames = new Set(ir.domain.map(e => e.name));
    
    // Check for undefined entities in relationships
    for (const entity of ir.domain) {
      if (entity.relationships) {
        for (const rel of entity.relationships) {
          if (!entityNames.has(rel.target)) {
            issues.push({
              id: 'CONS_001',
              severity: 'error',
              message: `Entity '${entity.name}' references undefined entity '${rel.target}'`,
              location: { section: 'domain' },
            });
          }
        }
      }
    }
  }

  private validateCompleteness(ir: AEIR, issues: SpecLintIssue[]): void {
    // Check for entities without required fields
    for (const entity of ir.domain) {
      const hasRequiredFields = entity.fields.some(f => f.required);
      if (!hasRequiredFields) {
        issues.push({
          id: 'COMP_001',
          severity: 'warn',
          message: `Entity '${entity.name}' has no required fields`,
          location: { section: 'domain' },
          suggestion: 'Consider marking key fields as required',
        });
      }
    }
  }

  private validateStrictSchema(ir: AEIR, issues: SpecLintIssue[]): void {
    const validator = createAEIRValidator();
    const result = validator.validate(ir);
    
    if (!result.success) {
      const readableErrors = validator.getReadableErrors((result as any).errors || []);
      const relaxed = process.env['AE_SPEC_RELAXED'] === '1';
      readableErrors.forEach((error, index) => {
        const item: SpecLintIssue = {
          id: `SCHEMA_${(index + 1).toString().padStart(3, '0')}`,
          severity: relaxed ? 'warn' : 'error',
          message: `Schema validation ${relaxed ? 'warning (relaxed mode)' : 'failed'} at ${error.path}: ${error.message}`,
          location: { section: error.path.split('.')[0] || 'root' },
          suggestion: relaxed ? 'Consider fixing to meet strict schema, or keep relaxed mode enabled' : 'Fix the schema validation error to ensure specification compliance'
        };
        issues.push(item);
      });
    }
  }

  private applyLenientNormalizations(ir: AEIR): AEIR {
    // Map enum-like types to string
    ir.domain = (ir.domain || []).map(ent => ({
      ...ent,
      fields: (ent.fields || []).map(f => {
        const t = String(f.type || '').toLowerCase();
        if (t.startsWith('enum:')) {
          return { ...f, type: 'string' };
        }
        return f;
      })
    }));
    // Invariant ID: generate UUID if not valid
    const uuidRe = /^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
    ir.invariants = (ir.invariants || []).map(inv => ({
      ...inv,
      id: uuidRe.test(String(inv.id)) ? inv.id : uuidv4(),
    }));
    return ir;
  }
}
