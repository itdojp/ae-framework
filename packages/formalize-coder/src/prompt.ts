import type { FormalPlan } from './types.js';

export const coderSystemPrompt =
  'You are a formalization coder. Convert a formal.yaml plan into a TLA+ module skeleton.';

export const FORMAL_CODER_REQUIRED_SECTIONS = [
  'MODULE header',
  'EXTENDS',
  'CONSTANTS (if any)',
  'VARIABLES',
  'Init',
  'Next',
  'Spec',
  'Invariants',
  'Liveness (if any)',
  'Assumptions (if any)',
];

export function formatFormalPlan(plan: FormalPlan | string) {
  if (typeof plan === 'string') {
    return plan;
  }
  return JSON.stringify(plan, null, 2);
}

export function buildCoderPrompt({
  plan,
  moduleName = 'Spec',
  context = '',
}: {
  plan: FormalPlan | string;
  moduleName?: string;
  context?: string;
}) {
  const planText = formatFormalPlan(plan);
  return [
    coderSystemPrompt,
    '',
    `Module Name: ${moduleName}`,
    '',
    'Formal Plan (formal.yaml or JSON equivalent):',
    planText || '(empty)',
    '',
    'Output Requirements:',
    '- Emit a TLA+ module skeleton using the plan fields.',
    '- Preserve action/invariant formulas as named definitions.',
    '- Ensure Init/Next are defined; Next should disjoin non-init actions.',
    '- Add Spec == Init /\\ [][Next]_vars for model checking.',
    '',
    'Required Sections:',
    ...FORMAL_CODER_REQUIRED_SECTIONS.map((section) => `- ${section}`),
    '',
    'Additional Context:',
    context || '(none)',
  ].join('\n');
}
