#!/usr/bin/env node
// Prompt joiner for CodeX: convert validator issues JSON into a concise
// revision instruction prompt for the LLM.
//
// Usage:
//  1) Generate issues JSON via stdio validate:
//     echo '{"action":"validate","args":{"inputPath":"spec/feature.ae-spec.md","relaxed":true,"maxWarnings":999}}' | pnpm run codex:spec:stdio > /tmp/validate.json
//  2) Make prompt:
//     pnpm run codex:spec:prompt -- /tmp/validate.json spec/feature.ae-spec.md > /tmp/revise.md
//  3) Feed /tmp/revise.md to your LLM agent and update the spec

import fs from 'fs';
import path from 'path';

function loadJSON(p) {
  try { return JSON.parse(fs.readFileSync(p, 'utf8')); } catch { return null; }
}

function fmtPrompt(issues, specPath) {
  const items = (issues || []).slice(0, 50);
  const bullets = items.map((i, idx) => `- [${i.severity}] ${i.message} (section: ${i.section})`).join('\n');
  return `Please revise the AE‑Spec to address the following validator findings. Preserve prior valid content.\n\nTarget file: ${specPath}\n\nConstraints:\n- Use only: string|number|boolean|date|uuid|email|url|json|array|object for field types\n- If enum-like fields are used, map to a supported base type (e.g., string)\n- Ensure invariants reference existing entities\n- Ensure API paths start with '/' and list items as '- METHOD /path - summary'\n\nFindings:\n${bullets}\n\nProduce updated AE‑Spec Markdown with sections: Glossary, Domain, Invariants, Use Cases, API, UI, NFR.`;
}

async function main() {
  const [,, issuesPath, specPath='spec/feature.ae-spec.md'] = process.argv;
  if (!issuesPath) {
    console.log('Usage: pnpm run codex:spec:prompt -- <issues.json> [specPath]');
    process.exit(0);
  }
  const raw = loadJSON(issuesPath);
  if (!raw || !raw.data) {
    console.error('Invalid issues JSON: expected top-level { data: { issues: [...] } }');
    process.exit(1);
  }
  const issues = raw.data.issues || [];
  const out = fmtPrompt(issues, specPath);
  process.stdout.write(out + '\n');
}

main().catch(e => { console.error(e?.message || String(e)); process.exit(1); });

