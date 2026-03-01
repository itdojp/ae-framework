import path from 'path';

export interface ContractFile {
  path: string; // relative to project root
  content: string;
}

export interface ContractsOptions {
  language?: 'ts';
  zodImport?: string; // e.g., "import { z } from 'zod'"
}

type SupportedType = 'unknown' | 'object' | 'array' | 'string' | 'number' | 'boolean';

interface TransitionEdge {
  from: string;
  to: string;
  condition?: string;
}

export interface ParsedFormalSpec {
  inputType: SupportedType;
  outputType: SupportedType;
  preconditions: string[];
  postconditions: string[];
  states: string[];
  transitions: TransitionEdge[];
  warnings: string[];
}

const DIRECTIVE_PATTERN = /^@([a-zA-Z_][\w-]*)\s+(.+)$/;
const SUPPORTED_DIRECTIVES = new Set(['input', 'output', 'pre', 'post', 'state', 'states', 'transition']);

const normalizeType = (raw: string): SupportedType | null => {
  const value = raw.trim().toLowerCase();
  if (value === 'object' || value === 'record' || value === 'map') return 'object';
  if (value === 'array' || value === 'list') return 'array';
  if (value === 'string') return 'string';
  if (value === 'number' || value === 'int' || value === 'integer' || value === 'float') return 'number';
  if (value === 'boolean' || value === 'bool') return 'boolean';
  if (value === 'unknown' || value === 'any') return 'unknown';
  return null;
};

const sanitizeStateName = (raw: string): string => {
  const cleaned = raw.trim().replace(/^['"]|['"]$/g, '');
  if (!cleaned) return '';
  const alnum = cleaned.replace(/[^a-zA-Z0-9_]/g, '_');
  if (!alnum) return '';
  if (!/^[A-Za-z_]/.test(alnum)) return `S_${alnum}`;
  return alnum;
};

const splitStates = (raw: string): string[] =>
  raw
    .split(/[|,]/)
    .map((item) => sanitizeStateName(item))
    .filter(Boolean);

const parseTransition = (raw: string): TransitionEdge | null => {
  const normalized = raw.trim();
  if (!normalized) return null;

  const [transitionPartRaw, ...conditionParts] = normalized.split(/\s+if\s+/i);
  const transitionPart = transitionPartRaw ?? '';
  const arrowIndex = transitionPart.indexOf('->');
  if (arrowIndex < 0) return null;

  const from = sanitizeStateName(transitionPart.slice(0, arrowIndex));
  const to = sanitizeStateName(transitionPart.slice(arrowIndex + 2));
  const condition = conditionParts.join(' if ').trim();
  if (!from || !to) return null;
  const edge: TransitionEdge = { from, to };
  if (condition) edge.condition = condition;
  return edge;
};

const unique = (values: string[]): string[] => [...new Set(values)];

const inferTypeFromSpec = (formalSpec: string, token: 'input' | 'output'): SupportedType | null => {
  const objectPattern = new RegExp(`\\b${token}\\b[^\\n]*[=:]\\s*\\{`, 'i');
  const arrayPattern = new RegExp(`\\b${token}\\b[^\\n]*[=:]\\s*\\[`, 'i');
  const stringPattern = new RegExp(`\\b${token}\\b[^\\n]*\\bstring\\b`, 'i');
  const numberPattern = new RegExp(`\\b${token}\\b[^\\n]*\\b(number|int|integer|float)\\b`, 'i');
  const booleanPattern = new RegExp(`\\b${token}\\b[^\\n]*\\b(bool|boolean)\\b`, 'i');

  if (objectPattern.test(formalSpec)) return 'object';
  if (arrayPattern.test(formalSpec)) return 'array';
  if (stringPattern.test(formalSpec)) return 'string';
  if (numberPattern.test(formalSpec)) return 'number';
  if (booleanPattern.test(formalSpec)) return 'boolean';
  return null;
};

const extractPredicateByName = (formalSpec: string, names: string[]): string[] => {
  const matches: string[] = [];
  for (const name of names) {
    const regex = new RegExp(`\\b${name}\\b\\s*==\\s*(.+)`, 'gi');
    for (const hit of formalSpec.matchAll(regex)) {
      const expr = String(hit[1] ?? '').trim();
      if (expr) matches.push(expr);
    }
  }
  return matches;
};

const extractStateSet = (formalSpec: string): string[] => {
  const patterns = [
    /\bstate\b\s*\\in\s*\{([^}]+)\}/i, // TLA+ style: state \in {...}
    /\bstate\b\s*in\s*\{([^}]+)\}/i, // generic style
  ];
  for (const pattern of patterns) {
    const match = formalSpec.match(pattern);
    if (match?.[1]) {
      return splitStates(match[1]);
    }
  }
  return [];
};

const extractArrowTransitions = (formalSpec: string): TransitionEdge[] => {
  const edges: TransitionEdge[] = [];
  for (const rawLine of formalSpec.split(/\r?\n/)) {
    const line = rawLine.trim().replace(/^(?:--+|\/\/+|#|;|\*)\s*/, '');
    if (!line.includes('->')) continue;
    const parsed = parseTransition(line);
    if (parsed) edges.push(parsed);
  }
  return edges;
};

const toZodExpr = (type: SupportedType): string => {
  switch (type) {
    case 'object':
      return 'z.record(z.unknown())';
    case 'array':
      return 'z.array(z.unknown())';
    case 'string':
      return 'z.string()';
    case 'number':
      return 'z.number()';
    case 'boolean':
      return 'z.boolean()';
    case 'unknown':
    default:
      return 'z.unknown()';
  }
};

const toConstArrayLiteral = (name: string, values: string[]): string => {
  if (values.length === 0) {
    return `export const ${name} = [] as const;\n`;
  }
  const lines = values.map((value) => `  ${JSON.stringify(value)},`).join('\n');
  return `export const ${name} = [\n${lines}\n] as const;\n`;
};

const renderPreconditionPredicate = (expr: string): { predicate: string; recognized: boolean } => {
  const normalized = expr.trim();
  if (!normalized) return { predicate: '(input) => input !== undefined', recognized: true };
  if (/typeok/i.test(normalized)) return { predicate: '(input) => input !== undefined', recognized: true };
  if (/input\s*!=\s*null/i.test(normalized)) return { predicate: '(input) => input != null', recognized: true };
  return { predicate: '(_input) => false', recognized: false };
};

const renderPostconditionPredicate = (expr: string): { predicate: string; recognized: boolean } => {
  const normalized = expr.trim();
  if (!normalized) return { predicate: '(_input, output) => output !== undefined', recognized: true };
  if (/output\s*!=\s*null/i.test(normalized)) return { predicate: '(_input, output) => output != null', recognized: true };
  return { predicate: '(_input, _output) => false', recognized: false };
};

const buildDefaultTransitions = (states: string[]): TransitionEdge[] => {
  if (states.length <= 1) return [];
  const edges: TransitionEdge[] = [];
  for (let i = 0; i < states.length - 1; i += 1) {
    const from = states[i]!;
    const to = states[i + 1]!;
    edges.push({ from, to, condition: 'default-sequence' });
  }
  return edges;
};

export function parseFormalSpec(formalSpec: string): ParsedFormalSpec {
  const warnings: string[] = [];
  const preconditions: string[] = [];
  const postconditions: string[] = [];
  const states: string[] = [];
  const transitions: TransitionEdge[] = [];
  let inputType: SupportedType | null = null;
  let outputType: SupportedType | null = null;
  let usedDirective = false;

  const lines = formalSpec.split(/\r?\n/);
  for (const raw of lines) {
    const line = raw.trim();
    if (!line) continue;
    const stripped = line.replace(/^(?:--+|\/\/+|#|;|\*)\s*/, '');
    const directiveMatch = stripped.match(DIRECTIVE_PATTERN);
    if (!directiveMatch) continue;
    const directive = String(directiveMatch[1] ?? '').toLowerCase();
    if (SUPPORTED_DIRECTIVES.has(directive)) usedDirective = true;
    const payload = String(directiveMatch[2] ?? '').trim();
    if (!payload) continue;

    if (directive === 'input') {
      const parsedType = normalizeType(payload);
      if (parsedType) {
        inputType = parsedType;
      } else {
        warnings.push(`Unsupported @input type: ${payload}`);
      }
      continue;
    }
    if (directive === 'output') {
      const parsedType = normalizeType(payload);
      if (parsedType) {
        outputType = parsedType;
      } else {
        warnings.push(`Unsupported @output type: ${payload}`);
      }
      continue;
    }
    if (directive === 'pre') {
      preconditions.push(payload);
      continue;
    }
    if (directive === 'post') {
      postconditions.push(payload);
      continue;
    }
    if (directive === 'state' || directive === 'states') {
      states.push(...splitStates(payload));
      continue;
    }
    if (directive === 'transition') {
      const transition = parseTransition(payload);
      if (transition) {
        transitions.push(transition);
      } else {
        warnings.push(`Invalid @transition syntax: ${payload}`);
      }
      continue;
    }
    warnings.push(`Unsupported directive @${directive}`);
  }

  if (!inputType) {
    inputType = inferTypeFromSpec(formalSpec, 'input') ?? 'unknown';
    if (inputType === 'unknown') warnings.push('Input type could not be inferred; using z.unknown().');
  }
  if (!outputType) {
    outputType = inferTypeFromSpec(formalSpec, 'output') ?? 'unknown';
    if (outputType === 'unknown') warnings.push('Output type could not be inferred; using z.unknown().');
  }

  if (preconditions.length === 0) {
    preconditions.push(...extractPredicateByName(formalSpec, ['TypeOK', 'Pre', 'Precondition']));
    if (preconditions.length === 0) {
      warnings.push('Precondition was not found; using schema validation only.');
    }
  }
  if (postconditions.length === 0) {
    postconditions.push(...extractPredicateByName(formalSpec, ['Post', 'Postcondition']));
    if (postconditions.length === 0) {
      warnings.push('Postcondition was not found; using schema validation only.');
    }
  }

  if (states.length === 0) {
    states.push(...extractStateSet(formalSpec));
  }
  if (states.length === 0) {
    states.push('Init', 'Next', 'Done');
    warnings.push('State set was not found; using default states Init/Next/Done.');
  }

  if (transitions.length === 0) {
    transitions.push(...extractArrowTransitions(formalSpec));
  }
  if (transitions.length === 0) {
    transitions.push(...buildDefaultTransitions(states));
    warnings.push('Transitions were not found; using default sequential transitions.');
  }

  if (!usedDirective) {
    warnings.push('No explicit @input/@output/@pre/@post/@state directives were detected.');
  }

  const normalizedStates = unique(states.map((state) => sanitizeStateName(state)).filter(Boolean));
  const normalizedTransitions = transitions
    .map((edge) => {
      const from = sanitizeStateName(edge.from);
      const to = sanitizeStateName(edge.to);
      const condition = edge.condition?.trim();
      const normalized: TransitionEdge = { from, to };
      if (condition) normalized.condition = condition;
      return normalized;
    })
    .filter((edge) => edge.from && edge.to);

  for (const edge of normalizedTransitions) {
    if (!normalizedStates.includes(edge.from)) normalizedStates.push(edge.from);
    if (!normalizedStates.includes(edge.to)) normalizedStates.push(edge.to);
  }

  return {
    inputType,
    outputType,
    preconditions: unique(preconditions.map((item) => item.trim()).filter(Boolean)),
    postconditions: unique(postconditions.map((item) => item.trim()).filter(Boolean)),
    states: normalizedStates,
    transitions: normalizedTransitions,
    warnings: unique(warnings),
  };
}

export function generateContractsFromParsedSpec(parsed: ParsedFormalSpec, opts: ContractsOptions = {}): ContractFile[] {
  const zodImport = opts.zodImport ?? "import { z } from 'zod'";
  const files: ContractFile[] = [];
  const generationWarnings = [...parsed.warnings];

  const preconditionPredicates =
    parsed.preconditions.length > 0
      ? parsed.preconditions
          .map((expr) => {
            const rendered = renderPreconditionPredicate(expr);
            if (!rendered.recognized) {
              generationWarnings.push(`Unrecognized @pre expression "${expr}" defaults to fail-closed predicate.`);
            }
            return `  // Derived from spec: ${expr}\n  ${rendered.predicate},`;
          })
          .join('\n')
      : '';
  const postconditionPredicates =
    parsed.postconditions.length > 0
      ? parsed.postconditions
          .map((expr) => {
            const rendered = renderPostconditionPredicate(expr);
            if (!rendered.recognized) {
              generationWarnings.push(`Unrecognized @post expression "${expr}" defaults to fail-closed predicate.`);
            }
            return `  // Derived from spec: ${expr}\n  ${rendered.predicate},`;
          })
          .join('\n')
      : '';
  const warningBlock = toConstArrayLiteral('generationWarnings', unique(generationWarnings));

  const schema = `${zodImport}\n\n${warningBlock}\nexport const InputSchema = ${toZodExpr(parsed.inputType)};\nexport const OutputSchema = ${toZodExpr(parsed.outputType)};\n`;
  files.push({ path: path.posix.join('src', 'contracts', 'schemas.ts'), content: schema });

  const prePost =
    `import { InputSchema, OutputSchema } from './schemas';\n\n` +
    `${warningBlock}\n` +
    `const DERIVED_PRECONDITIONS: Array<(input: unknown) => boolean> = [\n${preconditionPredicates}\n];\n\n` +
    `const DERIVED_POSTCONDITIONS: Array<(input: unknown, output: unknown) => boolean> = [\n${postconditionPredicates}\n];\n\n` +
    `export function pre(input: unknown): boolean {\n` +
    `  if (!InputSchema.safeParse(input).success) return false;\n` +
    `  return DERIVED_PRECONDITIONS.every((predicate) => predicate(input));\n` +
    `}\n\n` +
    `export function post(input: unknown, output: unknown): boolean {\n` +
    `  if (!InputSchema.safeParse(input).success) return false;\n` +
    `  if (!OutputSchema.safeParse(output).success) return false;\n` +
    `  return DERIVED_POSTCONDITIONS.every((predicate) => predicate(input, output));\n` +
    `}\n`;
  files.push({ path: path.posix.join('src', 'contracts', 'conditions.ts'), content: prePost });

  const states = parsed.states.length > 0 ? parsed.states : ['Init', 'Next', 'Done'];
  const stateUnion = states.map((state) => `'${state}'`).join(' | ');
  const transitionMapLines = states.map((state) => {
    const edges = parsed.transitions.filter((edge) => edge.from === state);
    if (edges.length === 0) {
      return `TRANSITIONS[${JSON.stringify(state)} as State] = [{ to: ${JSON.stringify(state)} as State, condition: 'self-loop' }];`;
    }
    const entries = edges
      .map((edge) => `{ to: ${JSON.stringify(edge.to)} as State, condition: ${JSON.stringify(edge.condition ?? 'unspecified')} }`)
      .join(', ');
    return `TRANSITIONS[${JSON.stringify(state)} as State] = [${entries}];`;
  });
  const machine =
    `${warningBlock}\n` +
    `export type State = ${stateUnion};\n` +
    `export type Transition = { to: State; condition: string };\n\n` +
    `const TRANSITIONS: Record<State, Transition[]> = Object.create(null);\n` +
    `${transitionMapLines.join('\n')}\n\n` +
    `export function next(state: State): State {\n` +
    `  const transitions = TRANSITIONS[state];\n` +
    `  if (!transitions || transitions.length === 0) return state;\n` +
    `  return transitions[0]!.to;\n` +
    `}\n\n` +
    `export function allowedTransitions(state: State): State[] {\n` +
    `  return (TRANSITIONS[state] ?? []).map((transition) => transition.to);\n` +
    `}\n`;
  files.push({ path: path.posix.join('src', 'contracts', 'machine.ts'), content: machine });

  return files;
}

/**
 * Generate runtime contracts from a formal spec string.
 * Supports explicit directives (`@input`, `@output`, `@pre`, `@post`, `@state`, `@transition`)
 * and falls back to lightweight heuristics when directives are absent.
 */
export function generateContractsFromFormalSpec(formalSpec: string, opts: ContractsOptions = {}): ContractFile[] {
  const parsed = parseFormalSpec(formalSpec);
  return generateContractsFromParsedSpec(parsed, opts);
}
