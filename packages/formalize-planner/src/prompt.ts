export const FORMAL_PLAN_SCHEMA_VERSION = '0.1.0';

export const FORMAL_PLAN_REQUIRED_FIELDS = [
  'schemaVersion',
  'metadata',
  'variables',
  'actions',
  'invariants',
];

export const plannerSystemPrompt =
  'You are a formalization planner. Convert requirements into a formal.yaml plan for TLA+ skeletons.';

export function buildPlannerPrompt({
  requirements = '',
  context = '',
}: { requirements?: string; context?: string } = {}) {
  return [
    plannerSystemPrompt,
    '',
    'Input Requirements:',
    requirements || '(none provided)',
    '',
    'Additional Context:',
    context || '(none)',
    '',
    'Output Format: YAML (formal.yaml) with the following fields:',
    `- schemaVersion: ${FORMAL_PLAN_SCHEMA_VERSION}`,
    '- metadata: { source, generatedAt }',
    '- variables: [ { name, type } ]',
    '- actions: [ { name, tla } ]',
    '- invariants: [ { name, tla } ]',
    '- requirements: [string] (optional)',
    '- constants: [ { name, type } ] (optional)',
    '- liveness: [ { name, tla } ] (optional)',
    '- assumptions: [ { name, tla } ] (optional)',
  ].join('\n');
}
