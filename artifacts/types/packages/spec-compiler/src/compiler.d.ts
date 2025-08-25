import { AEIR, CompileOptions, SpecLintReport } from './types.js';
export declare class AESpecCompiler {
    /**
     * Compile AE-Spec markdown to AE-IR JSON
     */
    compile(options: CompileOptions): Promise<AEIR>;
    /**
     * Lint AE-IR for quality issues with strict schema validation
     */
    lint(ir: AEIR): Promise<SpecLintReport>;
    private parseMarkdownToIR;
    private extractSections;
    private parseGlossary;
    private parseDomain;
    private parseInvariants;
    private parseUsecases;
    private parseStateMachines;
    private parseAPI;
    private parseUI;
    private parseNFR;
    private validateStructure;
    private validateBusinessLogic;
    private validateConsistency;
    private validateCompleteness;
    private validateStrictSchema;
}
