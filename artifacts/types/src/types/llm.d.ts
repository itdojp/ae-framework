export interface LLM {
    name: string;
    complete(input: {
        system?: string;
        prompt: string;
        temperature?: number;
    }): Promise<string>;
}
