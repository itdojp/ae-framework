/**
 * Git Hooks Setup for ae-framework Self-Improvement
 *
 * This module sets up git hooks to enforce TDD compliance during development
 */
export interface GitHooksSetupConfig {
    projectRoot: string;
    forceOverwrite: boolean;
    enableTDDEnforcement: boolean;
}
export declare class GitHooksSetup {
    private config;
    constructor(config?: Partial<GitHooksSetupConfig>);
    /**
     * Set up git hooks for TDD enforcement
     */
    setupGitHooks(): Promise<{
        success: boolean;
        hooksInstalled: string[];
        message: string;
    }>;
    /**
     * Install pre-commit hook
     */
    private installPreCommitHook;
    /**
     * Install pre-push hook for additional validation
     */
    private installPrePushHook;
    /**
     * Validate git hooks installation
     */
    validateGitHooks(): Promise<{
        preCommitInstalled: boolean;
        prePushInstalled: boolean;
        allHooksWorking: boolean;
        issues: string[];
    }>;
    /**
     * Uninstall git hooks (for cleanup)
     */
    uninstallGitHooks(): Promise<{
        success: boolean;
        hooksRemoved: string[];
        message: string;
    }>;
}
export declare const createGitHooksSetup: (config?: Partial<GitHooksSetupConfig>) => GitHooksSetup;
