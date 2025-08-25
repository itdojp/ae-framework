import { loadLLM } from '../../providers/index.js';
import { withRecorder } from '../../providers/recorder.js';

export async function agentComplete(prompt: string, system?: string, flags?: { record?: boolean; replay?: boolean; dir?: string }) {
  try {
    const mode = process.env.AE_RECORDER_MODE; // record|replay|off
    const wantReplay = flags?.replay ?? (mode === 'replay');
    const wantRecord = flags?.record ?? (mode === 'record');
    
    let llm = await loadLLM();
    
    if (wantReplay || wantRecord) {
      llm = withRecorder(llm, { dir: flags?.dir, replay: wantReplay });
    }
    
    console.log(`Using LLM provider: ${llm.name}`);
    
    const output = await llm.complete({ prompt, system });
    console.log(`[${llm.name}]`, output);
  } catch (error) {
    console.error('LLM completion failed:', error instanceof Error ? error.message : 'Unknown error');
    process.exit(1);
  }
}