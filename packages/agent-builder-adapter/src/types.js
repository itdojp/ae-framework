export const FLOW_SCHEMA_VERSION = '0.1.0';

export const NODE_KINDS = Object.freeze([
  'intent2formal',
  'formal2tests',
  'tests2code',
  'code2verify',
  'verify2operate',
]);

export const SIMULATION_STATUSES = Object.freeze([
  'simulated',
  'skipped',
]);
