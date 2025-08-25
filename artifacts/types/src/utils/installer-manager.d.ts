/**
 * Integrated Installer Manager for ae-framework
 * Manages project setup, dependency installation, and configuration
 */
export interface InstallationTemplate {
    id: string;
    name: string;
    description: string;
    category: 'web' | 'api' | 'cli' | 'library' | 'fullstack' | 'mobile';
    framework?: string;
    language: 'typescript' | 'javascript' | 'python' | 'rust' | 'go' | 'java' | 'elixir';
    dependencies: Dependency[];
    devDependencies?: Dependency[];
    scripts: Record<string, string>;
    files: TemplateFile[];
    configurations: Configuration[];
    postInstallSteps?: InstallStep[];
}
export interface Dependency {
    name: string;
    version?: string;
    optional?: boolean;
    condition?: string;
    alternatives?: string[];
}
export interface TemplateFile {
    path: string;
    content: string | (() => string);
    overwrite?: boolean;
    condition?: string;
}
export interface Configuration {
    file: string;
    format: 'json' | 'yaml' | 'env' | 'ini' | 'js' | 'ts' | 'elixir';
    content: Record<string, any> | string;
    merge?: boolean;
}
export interface InstallStep {
    type: 'command' | 'file' | 'config' | 'message';
    description: string;
    action: string | (() => Promise<void>);
    condition?: string;
    required?: boolean;
}
export interface InstallationContext {
    projectRoot: string;
    projectName: string;
    packageManager: 'npm' | 'yarn' | 'pnpm';
    nodeVersion?: string;
    existingPackageJson?: any;
    userPreferences?: Record<string, any>;
}
export interface InstallationResult {
    success: boolean;
    message: string;
    installedDependencies: string[];
    createdFiles: string[];
    configuredFiles: string[];
    executedSteps: string[];
    warnings: string[];
    errors: string[];
    duration: number;
}
export declare class InstallerManager {
    private templates;
    private projectRoot;
    constructor(projectRoot: string);
    /**
     * Get available installation templates
     */
    getAvailableTemplates(): InstallationTemplate[];
    /**
     * Get templates by category
     */
    getTemplatesByCategory(category: InstallationTemplate['category']): InstallationTemplate[];
    /**
     * Get template by ID
     */
    getTemplate(id: string): InstallationTemplate | undefined;
    /**
     * Install a template
     */
    installTemplate(templateId: string, context?: Partial<InstallationContext>): Promise<InstallationResult>;
    /**
     * Detect project type and suggest templates
     */
    suggestTemplates(): Promise<{
        suggestions: string[];
        reasoning: string[];
    }>;
    /**
     * Create a custom template
     */
    createCustomTemplate(template: InstallationTemplate): Promise<void>;
    /**
     * Update package manager detection
     */
    detectPackageManager(): Promise<'npm' | 'yarn' | 'pnpm'>;
    private loadDefaultTemplates;
    private prepareContext;
    private installDependencies;
    private createTemplateFiles;
    private applyConfigurations;
    private executePostInstallSteps;
    private ensurePackageJson;
    private updatePackageJsonScripts;
    private runPackageManagerCommand;
    private runCommand;
    private fileExists;
    private getProjectFiles;
    private saveCustomTemplate;
}
