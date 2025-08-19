"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.AESpecCompiler = void 0;
const fs_1 = require("fs");
class AESpecCompiler {
    /**
     * Compile AE-Spec markdown to AE-IR JSON
     */
    async compile(options) {
        const { inputPath, outputPath, validate = true } = options;
        try {
            const markdown = (0, fs_1.readFileSync)(inputPath, 'utf-8');
            const ir = this.parseMarkdownToIR(markdown);
            if (validate) {
                const lintResult = await this.lint(ir);
                if (!lintResult.passed) {
                    throw new Error(`Validation failed: ${lintResult.issues.length} issues found`);
                }
            }
            if (outputPath) {
                (0, fs_1.writeFileSync)(outputPath, JSON.stringify(ir, null, 2), 'utf-8');
            }
            return ir;
        }
        catch (error) {
            throw new Error(`Compilation failed: ${error.message}`);
        }
    }
    /**
     * Lint AE-IR for quality issues
     */
    async lint(ir) {
        const issues = [];
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
    parseMarkdownToIR(markdown) {
        const sections = this.extractSections(markdown);
        const timestamp = new Date().toISOString();
        return {
            version: '1.0.0',
            metadata: {
                name: sections.title || 'Untitled Specification',
                description: sections.description,
                created: timestamp,
                updated: timestamp,
            },
            glossary: this.parseGlossary(sections.glossary || ''),
            domain: this.parseDomain(sections.domain || ''),
            invariants: this.parseInvariants(sections.invariants || ''),
            usecases: this.parseUsecases(sections.usecases || ''),
            statemachines: this.parseStateMachines(sections.statemachines),
            api: this.parseAPI(sections.api || ''),
            ui: this.parseUI(sections.ui),
            nfr: this.parseNFR(sections.nfr),
        };
    }
    extractSections(markdown) {
        const sections = {};
        const lines = markdown.split('\n');
        let currentSection = '';
        let currentContent = [];
        for (const line of lines) {
            if (line.startsWith('# ')) {
                if (currentSection) {
                    sections[currentSection] = currentContent.join('\n').trim();
                }
                sections.title = line.substring(2).trim();
                currentSection = 'description';
                currentContent = [];
            }
            else if (line.startsWith('## ')) {
                if (currentSection) {
                    sections[currentSection] = currentContent.join('\n').trim();
                }
                currentSection = line.substring(3).trim().toLowerCase().replace(/\s+/g, '');
                currentContent = [];
            }
            else {
                currentContent.push(line);
            }
        }
        if (currentSection) {
            sections[currentSection] = currentContent.join('\n').trim();
        }
        return sections;
    }
    parseGlossary(content) {
        const glossary = [];
        const lines = content.split('\n');
        for (const line of lines) {
            const match = line.match(/^[-*]\s*\*\*(.+?)\*\*:\s*(.+)$/);
            if (match) {
                glossary.push({
                    term: match[1].trim(),
                    definition: match[2].trim(),
                });
            }
        }
        return glossary;
    }
    parseDomain(content) {
        const entities = [];
        const lines = content.split('\n');
        let currentEntity = null;
        for (const line of lines) {
            const entityMatch = line.match(/^###\s+(.+)$/);
            if (entityMatch) {
                if (currentEntity) {
                    entities.push(currentEntity);
                }
                currentEntity = {
                    name: entityMatch[1].trim(),
                    fields: [],
                };
            }
            else if (currentEntity) {
                const fieldMatch = line.match(/^[-*]\s*\*\*(.+?)\*\*\s*\((.+?)\)(?:\s*-\s*(.+))?$/);
                if (fieldMatch) {
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
    parseInvariants(content) {
        const invariants = [];
        const lines = content.split('\n');
        let counter = 1;
        for (const line of lines) {
            const match = line.match(/^[-*]\s*(.+)$/);
            if (match) {
                invariants.push({
                    id: `INV_${counter.toString().padStart(3, '0')}`,
                    description: match[1].trim(),
                    expression: match[1].trim(), // In real implementation, parse to formal expression
                    entities: [], // Extract from expression
                    severity: 'error',
                });
                counter++;
            }
        }
        return invariants;
    }
    parseUsecases(content) {
        const usecases = [];
        const sections = content.split(/^###\s+/m);
        for (const section of sections.slice(1)) {
            const lines = section.split('\n');
            const name = lines[0].trim();
            const usecase = {
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
                        description: stepMatch[1].trim(),
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
    parseStateMachines(content) {
        if (!content)
            return undefined;
        // Simplified state machine parsing - extend as needed
        return [];
    }
    parseAPI(content) {
        const apis = [];
        const lines = content.split('\n');
        for (const line of lines) {
            const match = line.match(/^[-*]\s*(GET|POST|PUT|PATCH|DELETE)\s+(.+?)(?:\s*-\s*(.+))?$/);
            if (match) {
                apis.push({
                    method: match[1],
                    path: match[2].trim(),
                    summary: match[3]?.trim(),
                });
            }
        }
        return apis;
    }
    parseUI(content) {
        if (!content)
            return undefined;
        // Simplified UI parsing - extend as needed
        return {
            viewModels: [],
            pages: [],
        };
    }
    parseNFR(content) {
        if (!content)
            return undefined;
        // Simplified NFR parsing - extend as needed
        return {
            performance: {},
            security: {},
        };
    }
    validateStructure(ir, issues) {
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
        if (ir.api.length === 0) {
            issues.push({
                id: 'STRUCT_003',
                severity: 'info',
                message: 'No API endpoints defined',
                location: { section: 'api' },
            });
        }
    }
    validateBusinessLogic(ir, issues) {
        // Check for entities without any business rules
        const entitiesWithRules = new Set(ir.invariants.flatMap(inv => inv.entities));
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
    validateConsistency(ir, issues) {
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
    validateCompleteness(ir, issues) {
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
}
exports.AESpecCompiler = AESpecCompiler;
//# sourceMappingURL=compiler.js.map