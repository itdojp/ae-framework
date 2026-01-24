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

const TEMPLATE_MAP: Record<string, string> = {
  'http-api': 'tests-first-http-api.md',
  queue: 'tests-first-queue.md',
  auth: 'tests-first-auth.md',
  math: 'tests-first-math.md',
};

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
  const intentBlock = intent ? `# Intent\n${intent}\n\n` : '';
  return `${intentBlock}${templateContent}`;
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
