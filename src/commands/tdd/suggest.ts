import { existsSync, readFileSync, writeFileSync } from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import { safeExit } from '../../utils/safe-exit.js';

export type TestsSuggestOptions = {
  template?: string;
  intent?: string;
  input?: string;
  output?: string;
};

export type TestsSuggestTemplateVariables = {
  intent: string;
  auth_type: string;
  roles: string;
  resources: string;
};

const TEMPLATE_MAP: Record<string, string> = {
  'http-api': 'tests-first-http-api.md',
  queue: 'tests-first-queue.md',
  auth: 'tests-first-auth.md',
  math: 'tests-first-math.md',
};

const FALLBACK_VALUE = 'unspecified';
const PLACEHOLDER_REGEX = /\{(intent|auth_type|roles|resources)\}/g;
const KNOWN_AUTH_TYPES = [
  { label: 'OAuth2', pattern: /\boauth2?\b/i },
  { label: 'JWT', pattern: /\bjwt\b/i },
  { label: 'Session', pattern: /\bsession\b/i },
  { label: 'API Key', pattern: /\bapi[_\s-]?key\b/i },
  { label: 'Basic Auth', pattern: /\bbasic auth\b/i },
];
const KNOWN_ROLES = ['admin', 'user', 'operator', 'auditor', 'guest', 'member'];

export function resolveTestsTemplate(template: string) {
  const mapped = TEMPLATE_MAP[template] ?? template;
  const moduleDir = path.dirname(fileURLToPath(import.meta.url));
  const promptRoots = [
    path.join(process.cwd(), 'templates', 'prompts'),
    findPromptRoot(moduleDir),
  ].filter(Boolean) as string[];

  const rawCandidates = [
    template,
    mapped,
    ...promptRoots.map((root) => path.join(root, mapped)),
  ];
  const candidates = Array.from(new Set(rawCandidates));

  for (const candidate of candidates) {
    if (existsSync(candidate)) {
      return candidate;
    }
  }

  const availableTemplates = Object.keys(TEMPLATE_MAP).join(', ');
  const searchedPaths = candidates.join(', ');
  throw new Error(
    `Template not found: "${template}". ` +
      `Available templates: ${availableTemplates}. ` +
      `Tried paths: ${searchedPaths}`,
  );
}

export function buildTestsSuggestOutput(templateContent: string, intentText?: string) {
  const intent = (intentText ?? '').trim();
  const variables = resolveTestsSuggestTemplateVariables(intentText);
  const renderedTemplate = applyTestsSuggestTemplateVariables(templateContent, variables);
  const intentBlock = intent ? `# Intent\n${intent}\n\n` : '';
  return `${intentBlock}${renderedTemplate}`;
}

export function testsSuggest(options: TestsSuggestOptions) {
  const templateName = options.template ?? 'http-api';
  const templatePath = resolveTestsTemplate(templateName);
  const templateContent = readFileSync(templatePath, 'utf8');
  if (options.input && options.intent) {
    console.warn(
      '⚠️ Both --input and --intent were provided; using --input and ignoring --intent.',
    );
  }
  const intentText = options.input ? readFileSync(options.input, 'utf8') : options.intent;
  const output = buildTestsSuggestOutput(templateContent, intentText);

  if (options.output) {
    writeFileSync(options.output, output, 'utf8');
    console.log(`✅ Wrote tests-first prompt to ${options.output}`);
    return;
  }

  process.stdout.write(output);
}

export function handleTestsSuggest(options: TestsSuggestOptions) {
  try {
    testsSuggest(options);
  } catch (error: unknown) {
    const message = error instanceof Error ? error.message : 'Unknown error';
    console.error(`❌ ${message}`);
    safeExit(1);
  }
}

function findPromptRoot(startDir: string) {
  let current = startDir;
  for (let depth = 0; depth < 6; depth += 1) {
    const candidate = path.join(current, 'templates', 'prompts');
    if (existsSync(candidate)) {
      return candidate;
    }
    const parent = path.dirname(current);
    if (parent === current) {
      break;
    }
    current = parent;
  }
  return undefined;
}

function normalizeListValue(value: string) {
  const normalized = value
    .replace(/^\[|\]$/g, '')
    .split(/[,\|;]/)
    .map((entry) => entry.trim())
    .filter(Boolean);
  return normalized.length > 0 ? normalized.join(', ') : FALLBACK_VALUE;
}

function extractStructuredValues(text: string) {
  const values: Partial<TestsSuggestTemplateVariables> = {};
  const lines = text.split(/\r?\n/);
  for (const line of lines) {
    const match = line.match(/^\s*(?:[-*]\s*)?([a-z_][a-z0-9_-]*)\s*[:=]\s*(.+?)\s*$/i);
    if (!match) {
      continue;
    }
    const rawKey = match[1];
    const rawValue = match[2];
    if (!rawKey || !rawValue) {
      continue;
    }
    const key = rawKey.toLowerCase();
    const value = rawValue.trim();
    if (!value) {
      continue;
    }
    if (key === 'intent') {
      values.intent = value;
    } else if (key === 'auth_type' || key === 'authtype' || key === 'auth-type') {
      values.auth_type = value;
    } else if (key === 'roles') {
      values.roles = normalizeListValue(value);
    } else if (key === 'resources') {
      values.resources = normalizeListValue(value);
    }
  }
  return values;
}

function inferAuthType(text: string) {
  for (const authType of KNOWN_AUTH_TYPES) {
    if (authType.pattern.test(text)) {
      return authType.label;
    }
  }
  return FALLBACK_VALUE;
}

function inferRoles(text: string) {
  const roles = KNOWN_ROLES.filter((role) => {
    const pattern = new RegExp(`\\b${role}\\b`, 'i');
    return pattern.test(text);
  });
  return roles.length > 0 ? roles.join(', ') : FALLBACK_VALUE;
}

function inferResources(text: string) {
  const routeMatches = Array.from(text.matchAll(/\/[a-z0-9_/-]+/gi))
    .map((match) => match[0].trim())
    .filter(Boolean);
  if (routeMatches.length > 0) {
    return Array.from(new Set(routeMatches)).join(', ');
  }
  return FALLBACK_VALUE;
}

export function resolveTestsSuggestTemplateVariables(intentText?: string): TestsSuggestTemplateVariables {
  const text = (intentText ?? '').trim();
  const structured = extractStructuredValues(text);
  return {
    intent: structured.intent ?? (text || FALLBACK_VALUE),
    auth_type: structured.auth_type ?? inferAuthType(text),
    roles: structured.roles ?? inferRoles(text),
    resources: structured.resources ?? inferResources(text),
  };
}

export function applyTestsSuggestTemplateVariables(
  templateContent: string,
  variables: TestsSuggestTemplateVariables,
) {
  return templateContent.replace(PLACEHOLDER_REGEX, (_placeholder, key: string) => {
    if (key === 'intent') {
      return variables.intent;
    }
    if (key === 'auth_type') {
      return variables.auth_type;
    }
    if (key === 'roles') {
      return variables.roles;
    }
    if (key === 'resources') {
      return variables.resources;
    }
    return FALLBACK_VALUE;
  });
}
