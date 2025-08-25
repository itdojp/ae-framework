interface PhaseState {
    entities: Record<string, EntityDefinition>;
    ui_preferences?: UIPreferences;
    relationships?: Record<string, any>;
}
interface EntityDefinition {
    description: string;
    attributes: Record<string, AttributeDefinition>;
    constraints?: any;
    acceptance_criteria?: string[];
}
interface AttributeDefinition {
    type: string;
    required: boolean;
    validation?: string;
    description: string;
    default?: any;
}
interface UIPreferences {
    theme?: string;
    layout?: string;
    components?: string;
    styling?: string;
    forms?: string;
    validation?: string;
    data_fetching?: string;
    testing?: string;
}
interface GeneratorOptions {
    outputDir: string;
    dryRun?: boolean;
    overwrite?: boolean;
    targetEntity?: string;
}
interface GenerationResult {
    success: boolean;
    files: string[];
    error?: string;
}
export declare class UIScaffoldGenerator {
    private phaseState;
    private options;
    private templatesDir;
    constructor(phaseState: PhaseState, options: GeneratorOptions);
    private findFrameworkRoot;
    generateAll(): Promise<Record<string, GenerationResult>>;
    private generateEntityUI;
    private buildTemplateContext;
    private findDisplayNameField;
    private findDescriptionField;
    private findStatusField;
    private getEditableAttributes;
    private getDisplayAttributes;
    private getCardDisplayFields;
    private getTimestampFields;
    private getRequiredFormFields;
    private getOptionalFormFields;
    private getEnumOptions;
    private renderTemplate;
    private writeFile;
    validatePhaseState(): {
        valid: boolean;
        errors: string[];
        entityCount: number;
        uiFramework: string;
    };
    private registerHandlebarsHelpers;
}
export {};
