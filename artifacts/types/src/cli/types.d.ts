export interface AEFrameworkConfig {
    version: string;
    name: string;
    description: string;
    phases: Record<string, Phase>;
    guards: Guard[];
    cli: CLIConfig;
    templates: TemplateConfig;
    integrations: IntegrationConfig;
    metrics: MetricsConfig;
}
export interface Phase {
    name: string;
    description: string;
    required_artifacts: string[];
    validation: string[];
    enforce_red_first?: boolean;
    block_code_without_test?: boolean;
    mandatory_test_run?: boolean;
    coverage_threshold?: number;
    prerequisites?: Prerequisite[];
}
export interface Prerequisite {
    phase: string;
    status: string;
    validation: string;
}
export interface Guard {
    name: string;
    description: string;
    rule: string;
    enforcement: 'strict' | 'warning';
}
export interface CLIConfig {
    checkpoint_validation: boolean;
    interactive_mode: boolean;
    auto_validation: boolean;
    commands: Record<string, CommandConfig>;
}
export interface CommandConfig {
    description: string;
    usage: string;
}
export interface TemplateConfig {
    test_first: {
        enabled: boolean;
        path: string;
    };
    phase_transitions: {
        enabled: boolean;
        require_validation: boolean;
    };
    standard_prompts: {
        enabled: boolean;
        path: string;
    };
}
export interface IntegrationConfig {
    git: {
        pre_commit_hooks: boolean;
        prevent_commit_on_red: boolean;
    };
    ide: {
        vscode_extension: boolean;
        guard_notifications: boolean;
    };
    ci_cd: {
        validate_on_push: boolean;
        block_merge_on_violations: boolean;
    };
}
export interface MetricsConfig {
    track_tdd_violations: boolean;
    phase_timing: boolean;
    coverage_trends: boolean;
    export: {
        format: string;
        path: string;
    };
}
export interface ValidationResult {
    success: boolean;
    message?: string;
    details: ValidationDetail[];
}
export interface ValidationDetail {
    check: string;
    passed: boolean;
    message?: string;
}
export interface GuardResult {
    success: boolean;
    message?: string;
}
export interface PhaseCheckpoint {
    beforeCode: {
        required: string[];
        validate: () => Promise<boolean>;
    };
    afterCode: {
        required: string[];
        validate: () => Promise<boolean>;
    };
}
