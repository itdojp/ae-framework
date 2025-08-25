import { AEFrameworkConfig } from '../types.js';
export declare class ConfigLoader {
    static load(configPath?: string): AEFrameworkConfig;
    private static validateAndSetDefaults;
    private static getDefaultConfig;
}
