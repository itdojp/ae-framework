export interface LLM {
  name: string;
  complete(input: { 
    system?: string; 
    prompt: string; 
    temperature?: number; 
  }): Promise<string>;
}

function withTimeout(llm: LLM, timeoutMs: number = 5000): LLM {
  return {
    name: llm.name,
    async complete(input) {
      const timeoutPromise = new Promise<string>((_, reject) => {
        setTimeout(() => reject(new Error('LLM timeout')), timeoutMs);
      });
      
      try {
        return await Promise.race([llm.complete(input), timeoutPromise]);
      } catch (error) {
        if (error instanceof Error && error.message === 'LLM timeout') {
          console.warn(`[${llm.name}] Timed out after ${timeoutMs}ms, falling back to echo`);
          const echoProvider = (await import('./llm-echo.js')).default;
          return await echoProvider.complete(input);
        }
        
        // For other errors, also fallback to echo
        console.warn(`[${llm.name}] Failed with error, falling back to echo:`, error instanceof Error ? error.message : 'Unknown error');
        const echoProvider = (await import('./llm-echo.js')).default;
        return await echoProvider.complete(input);
      }
    }
  };
}

export async function loadLLM(): Promise<LLM> {
  if (process.env.ANTHROPIC_API_KEY) {
    try {
      const llm = (await import('./llm-anthropic.js')).default;
      return withTimeout(llm);
    } catch (error) {
      console.warn('Anthropic SDK not available, falling back to echo');
    }
  }
  
  if (process.env.OPENAI_API_KEY) {
    try {
      const llm = (await import('./llm-openai.js')).default;
      return withTimeout(llm);
    } catch (error) {
      console.warn('OpenAI SDK not available, falling back to echo');
    }
  }
  
  if (process.env.GEMINI_API_KEY) {
    try {
      const llm = (await import('./llm-gemini.js')).default;
      return withTimeout(llm);
    } catch (error) {
      console.warn('Gemini SDK not available, falling back to echo');
    }
  }
  
  return (await import('./llm-echo.js')).default;
}