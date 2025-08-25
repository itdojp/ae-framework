import { loadLLM } from '../../providers/index.js';
import { withRecorder } from '../../providers/recorder.js';

export async function agentComplete(prompt: string, system?: string, flags?: { record?: boolean; replay?: boolean; dir?: string }) {
  // Enhanced flag interpretation
  const mode = process.env.AE_RECORDER_MODE; // record|replay|off
  
  // Error if both --record and --replay are specified
  if (flags?.record && flags?.replay) {
    console.error('Error: Cannot specify both --record and --replay flags');
    process.exit(1);
  }
  
  // Priority: explicit flags > environment variable
  let wantReplay = false;
  let wantRecord = false;
  
  if (flags?.replay) {
    wantReplay = true;
  } else if (flags?.record) {
    wantRecord = true;
  } else if (mode === 'replay') {
    wantReplay = true;
  } else if (mode === 'record') {
    wantRecord = true;
  }
  
  // Use default cassette directory if not specified
  const cassetteDir = flags?.dir ?? 'artifacts/cassettes';
  
  // Start execution log with prompt summary
  const promptSummary = prompt.length > 100 ? `${prompt.slice(0, 100)}...` : prompt;
  console.log(`[ae][agent] Starting completion: "${promptSummary}"`);
  
  if (wantRecord) {
    console.log(`[ae][agent] Mode: RECORD (cassettes -> ${cassetteDir})`);
  } else if (wantReplay) {
    console.log(`[ae][agent] Mode: REPLAY (cassettes <- ${cassetteDir})`);
  } else {
    console.log(`[ae][agent] Mode: LIVE`);
  }
  
  try {
    let llm = await loadLLM();
    
    if (wantReplay || wantRecord) {
      llm = withRecorder(llm, { dir: cassetteDir, replay: wantReplay });
    }
    
    console.log(`[ae][agent] Provider: ${llm.name}`);
    
    const output = await llm.complete({ prompt, system });
    
    // End execution log with character count
    console.log(`[ae][agent] Completed: ${output.length} characters`);
    console.log(`[${llm.name}]`, output);
  } catch (error) {
    console.error('[ae][agent] LLM completion failed:', error instanceof Error ? error.message : 'Unknown error');
    process.exit(1);
  }
}