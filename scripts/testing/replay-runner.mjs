#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return undefined; } }
function writeJson(p,obj){ fs.mkdirSync(path.dirname(p),{recursive:true}); fs.writeFileSync(p, JSON.stringify(obj,null,2)); }

function parseArgs(argv){
  const out={};
  for(let i=2;i<argv.length;i++){
    const a=argv[i];
    if(a.startsWith('--focus=')) out.focus=a.slice(8);
  }
  return out;
}

function applyEvent(state, e){
  // Placeholder apply; real logic lives in core/adapters. Here we only simulate counters.
  const qty = e?.payload?.qty ?? 0;
  switch(e?.name){
    case 'ItemReceived': state.onHand = (state.onHand??0) + qty; break;
    case 'ItemAllocated': state.allocated = (state.allocated??0) + qty; break;
    case 'ItemShipped': state.onHand = (state.onHand??0) - qty; state.allocated = Math.max((state.allocated??0)-qty,0); break;
    default: break;
  }
}

function checkInvariants(state){
  const violations=[];
  const disable = new Set((process.env.REPLAY_DISABLE || '').split(',').map(s=>s.trim()).filter(Boolean));
  const only = new Set((process.env.REPLAY_ONLY || '').split(',').map(s=>s.trim()).filter(Boolean));
  const onHandMin = Number.isFinite(Number(process.env.REPLAY_ONHAND_MIN)) ? Number(process.env.REPLAY_ONHAND_MIN) : 0;

  const run = (name) => (only.size>0 ? only.has(name) : !disable.has(name));

  // inv: allocated <= onHand
  if (run('allocated_le_onhand')){
    if ((state.allocated??0) > (state.onHand??0)) violations.push('allocated <= onHand');
  }

  // inv: onHand >= min
  if (run('onhand_min')){
    if ((state.onHand??0) < onHandMin) violations.push(`onHand >= ${onHandMin}`);
  }

  return violations;
}

async function main(){
  const args=parseArgs(process.argv);
  const focus=args.focus; // optional traceId filter (not used in sample, but kept for compatibility)
  const inputPath = process.env.REPLAY_INPUT || 'artifacts/domain/events.json';
  const outputPath = process.env.REPLAY_OUTPUT || 'artifacts/domain/replay.summary.json';
  const strict = (process.env.REPLAY_STRICT ?? '1') !== '0';
  const events = readJson(inputPath) || [];
  const state={ onHand:0, allocated:0 };
  for (const e of events){ applyEvent(state, e); }
  const violations = checkInvariants(state);
  const traceId = (Array.isArray(events) && events[0]?.traceId) ? events[0].traceId : (focus || 'replay-unknown');
  const summary = { traceId, totalEvents: events.length, finalState: state, violatedInvariants: violations };
  writeJson(outputPath, summary);
  const ok = violations.length===0;
  const detail = (process.env.REPLAY_PRINT_SUMMARY==='1');
  console.log(`${ok ? '✓' : '✗'} replay checked ${events.length} events; violations=${violations.length}; output=${outputPath}`);
  if (detail) console.log('summary:', JSON.stringify(summary,null,2));
  process.exit(strict ? (ok?0:1) : 0);
}

main().catch(err=>{ console.error('replay-runner error:', err); process.exit(1); });
