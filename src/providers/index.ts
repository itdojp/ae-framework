export interface LLM {
  name: string;
  complete(input: { 
    system?: string; 
    prompt: string; 
    temperature?: number; 
  }): Promise<string>;
}

// Cache echo provider to avoid repeated imports
let echoProviderPromise: Promise<{ default: LLM }> | null = null;

async function fallbackToEcho(input: { system?: string; prompt: string; temperature?: number }): Promise<string> {
  if (!echoProviderPromise) {
    echoProviderPromise = import('./llm-echo.js');
  }
  const echoProvider = (await echoProviderPromise).default;
  return await echoProvider.complete(input);
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
          return await fallbackToEcho(input);
        }
        
        // For other errors, also fallback to echo
        console.warn(`[${llm.name}] Failed with error, falling back to echo:`, error instanceof Error ? error.message : 'Unknown error');
        return await fallbackToEcho(input);
      }
    }
  };
}

async function has(pkg: string): Promise<boolean> {
  try {
    await eval(`import("${pkg}")`);
    return true;
  } catch {
    return false;
  }
}

export async function loadLLM(): Promise<LLM> {
  if (process.env['ANTHROPIC_API_KEY'] && await has('@anthropic-ai/sdk')) {
    try {
      const llm = (await import('./llm-anthropic.js')).default;
      return withTimeout(llm);
    } catch (error) {
      console.warn('Anthropic provider failed, falling back to echo');
    }
  }
  
  if (process.env['OPENAI_API_KEY'] && await has('openai')) {
    try {
      const llm = (await import('./llm-openai.js')).default;
      return withTimeout(llm);
    } catch (error) {
      console.warn('OpenAI provider failed, falling back to echo');
    }
  }
  
  if (process.env['GEMINI_API_KEY'] && await has('@google/generative-ai')) {
    try {
      const llm = (await import('./llm-gemini.js')).default;
      return withTimeout(llm);
    } catch (error) {
      console.warn('Gemini provider failed, falling back to echo');
    }
  }
  
  return (await import('./llm-echo.js')).default;
}
