export interface LLM {
  name: string;
  complete(input: { 
    system?: string; 
    prompt: string; 
    temperature?: number; 
  }): Promise<string>;
}

export async function loadLLM(): Promise<LLM> {
  if (process.env.ANTHROPIC_API_KEY) {
    try {
      return (await import('./llm-anthropic.js')).default;
    } catch (error) {
      console.warn('Anthropic SDK not available, falling back to echo');
    }
  }
  
  if (process.env.OPENAI_API_KEY) {
    try {
      return (await import('./llm-openai.js')).default;
    } catch (error) {
      console.warn('OpenAI SDK not available, falling back to echo');
    }
  }
  
  if (process.env.GEMINI_API_KEY) {
    try {
      return (await import('./llm-gemini.js')).default;
    } catch (error) {
      console.warn('Gemini SDK not available, falling back to echo');
    }
  }
  
  return (await import('./llm-echo.js')).default;
}