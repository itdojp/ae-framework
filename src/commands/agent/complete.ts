import { loadLLM } from '../../providers/index.js';

export async function agentComplete(prompt: string, system?: string) {
  try {
    const llm = await loadLLM();
    console.log(`Using LLM provider: ${llm.name}`);
    
    const output = await llm.complete({ prompt, system });
    console.log(`[${llm.name}]`, output);
  } catch (error) {
    console.error('LLM completion failed:', error instanceof Error ? error.message : 'Unknown error');
    process.exit(1);
  }
}