import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'fs';
import path from 'path';
import { safeExit } from '../../utils/safe-exit.js';

export type TestsScaffoldOptions = {
  input: string;
  out?: string;
  specId?: string;
  property?: boolean;
  contract?: boolean;
  regression?: boolean;
  overwrite?: boolean;
};

type FileEntry = {
  relativePath: string;
  content: string;
};

export type ScaffoldGenerationOptions = {
  property?: boolean;
  contract?: boolean;
  regression?: boolean;
};

/**
 * Bullet line parser used across acceptance extraction:
 * - supports "-" / "*" bullets
 * - supports optional markdown checkboxes
 * - keeps indentation so nested bullets can be distinguished from AC items
 */
const MARKDOWN_BULLET_RE = /^(\s*)[-*]\s*(?:\[[ xX]\]\s*)?(.*)$/;
const ACCEPTANCE_HEADING_RE = /^#{2,6}\s+.*(Acceptance Criteria|Acceptance|受入基準)/i;
const AC_PREFIX_RE = /^AC[-_ ]?\d+\s*(?:\([^)]*\))?:\s*(.*)$/i;
const GWT_LINE_RE = /^(Given|When|Then)\b.*$/i;

function parseBulletLine(line: string): { indent: number; text: string } | null {
  const match = line.match(MARKDOWN_BULLET_RE);
  if (!match) {
    return null;
  }
  const indent = (match[1] ?? '').length;
  const text = (match[2] ?? '').trim();
  return { indent, text };
}

function stripAcPrefix(text: string): string {
  const ac = text.match(AC_PREFIX_RE);
  const body = ac?.[1] ?? text;
  return body.trim().replace(/[:：]\s*$/, '').trim();
}

export function extractAcceptanceCriteria(markdown: string): string[] {
  const lines = markdown.split(/\r?\n/);
  const start = lines.findIndex((line) =>
    ACCEPTANCE_HEADING_RE.test(line.trim()),
  );

  const candidates: string[] = [];
  if (start >= 0) {
    let baseIndent: number | null = null;
    for (let i = start + 1; i < lines.length; i += 1) {
      const line = lines[i] ?? '';
      const trimmed = line.trim();
      if (/^#{1,6}\s+/.test(trimmed)) {
        break;
      }

      const bullet = parseBulletLine(line);
      if (!bullet) {
        continue;
      }
      if (baseIndent === null) {
        baseIndent = bullet.indent;
      }
      if (bullet.indent !== baseIndent) {
        continue;
      }

      let body = stripAcPrefix(bullet.text);
      const gwtParts: string[] = [];
      let j = i + 1;
      for (; j < lines.length; j += 1) {
        const nextLine = lines[j] ?? '';
        const nextTrimmed = nextLine.trim();
        if (/^#{1,6}\s+/.test(nextTrimmed)) {
          break;
        }

        const nextBullet = parseBulletLine(nextLine);
        if (nextBullet) {
          if (nextBullet.indent <= baseIndent) {
            break;
          }
          if (GWT_LINE_RE.test(nextBullet.text)) {
            gwtParts.push(nextBullet.text);
          }
          continue;
        }

        if (nextTrimmed.length === 0) {
          continue;
        }

        if (GWT_LINE_RE.test(nextTrimmed)) {
          gwtParts.push(nextTrimmed);
        } else if (!body) {
          body = nextTrimmed;
        }
      }
      const criterion = [body, ...gwtParts].filter(Boolean).join(' ').trim();
      if (criterion.length > 0) {
        candidates.push(criterion);
      }
      i = j - 1;
    }
    // Acceptance section exists: do not fall back to whole-document parsing.
    // This avoids accidentally treating NFR/checklist bullets as AC.
    return normalizeCriteria(candidates);
  }

  // No Acceptance heading: accept explicit AC-prefixed bullets only.
  for (const line of lines) {
    const bullet = parseBulletLine(line);
    if (!bullet) {
      continue;
    }
    const acMatch = bullet.text.match(AC_PREFIX_RE);
    if (acMatch?.[1]) {
      candidates.push(acMatch[1].trim());
    }
  }

  return normalizeCriteria(candidates);
}

function normalizeCriteria(criteria: string[]): string[] {
  return criteria
    .map((item) => item.replace(/\s+/g, ' ').trim())
    .filter((item) => item.length > 0);
}

function deriveSpecId(inputPath: string, override?: string): string {
  const raw = (override || path.basename(inputPath, path.extname(inputPath))).trim();
  return (
    raw
      .toLowerCase()
      .replace(/[^a-z0-9._-]+/g, '-')
      .replace(/-+/g, '-')
      .replace(/^-|-$/g, '') || 'spec'
  );
}

function splitGivenWhenThen(text: string): { given: string; when: string; then: string } | null {
  const normalized = text.replace(/\s+/g, ' ').trim();
  const whenIndex = normalized.search(/\bWhen\b/i);
  if (whenIndex < 0) {
    return null;
  }

  const thenRelativeIndex = normalized.slice(whenIndex + 4).search(/\bThen\b/i);
  if (thenRelativeIndex < 0) {
    return null;
  }

  const thenIndex = whenIndex + 4 + thenRelativeIndex;
  const given = normalized.slice(0, whenIndex).trim();
  const when = normalized.slice(whenIndex, thenIndex).trim();
  const then = normalized.slice(thenIndex).trim();
  if (!/^Given\b/i.test(given) || !/^When\b/i.test(when) || !/^Then\b/i.test(then)) {
    return null;
  }

  return { given: given.trim(), when: when.trim(), then: then.trim() };
}

function buildFeatureContent(specId: string, criteria: string[]): string {
  const lines: string[] = [];
  lines.push(`Feature: ${specId}`);
  lines.push('  # Generated by ae tests:scaffold');
  lines.push('');

  criteria.forEach((criterion, index) => {
    const scenarioName = `AC-${index + 1}: ${criterion}`;
    const gwt = splitGivenWhenThen(criterion);
    lines.push(`  Scenario: ${scenarioName}`);
    if (gwt) {
      lines.push(`    ${gwt.given}`);
      lines.push(`    ${gwt.when}`);
      lines.push(`    ${gwt.then}`);
    } else {
      lines.push('    Given TODO: setup precondition');
      lines.push('    When TODO: execute behavior');
      lines.push(`    Then ${criterion}`);
    }
    lines.push('');
  });

  return `${lines.join('\n').trimEnd()}\n`;
}

function buildAcceptanceMapContent(specId: string, criteria: string[]): string {
  const lines: string[] = [];
  lines.push(`# Acceptance Map: ${specId}`);
  lines.push('');
  lines.push('| AC | Criterion | Test Artifact | Status |');
  lines.push('| --- | --- | --- | --- |');
  criteria.forEach((criterion, index) => {
    lines.push(`| AC-${index + 1} | ${criterion} | \`bdd/${specId}.feature\` | TODO |`);
  });
  lines.push('');
  lines.push('## Notes');
  lines.push('- Fill Test Artifact with actual test file paths after implementation.');
  return `${lines.join('\n').trimEnd()}\n`;
}

function buildPropertyTestContent(specId: string): string {
  return `import { describe, it, expect } from 'vitest';\n` +
    `import fc from 'fast-check';\n\n` +
    `// Property-based tests for spec "${specId}".\n` +
    `//\n` +
    `// This is a scaffolded test. Replace the generator and assertions below\n` +
    `// with domain-specific properties and invariants derived from the\n` +
    `// acceptance criteria.\n` +
    `//\n` +
    `// Example patterns:\n` +
    `// - Idempotence: f(f(x)) === f(x)\n` +
    `// - Inverse: g(f(x)) === x\n` +
    `// - Preservation: an input property is preserved by the output\n` +
    `// - Ordering: outputs stay sorted/monotonic for ordered inputs\n` +
    `//\n` +
    `// TODO: Replace this placeholder with meaningful properties.\n` +
    `describe('property:${specId}', () => {\n` +
    `  it('satisfies domain invariants for all valid inputs', () => {\n` +
    `    fc.assert(\n` +
    `      fc.property(\n` +
    `        // TODO: Replace fc.anything() with domain-specific arbitrary.\n` +
    `        fc.anything(),\n` +
    `        (input) => {\n` +
    `          // TODO: Replace with assertions that encode your invariant.\n` +
    `          expect(input).toBeDefined();\n` +
    `        },\n` +
    `      ),\n` +
    `    );\n` +
    `  });\n` +
    `});\n`;
}

function buildContractTestContent(specId: string, criteria: string[]): string {
  const rows = criteria
    .map((criterion, index) => `    ['AC-${index + 1}', ${JSON.stringify(criterion)}],`)
    .join('\n');

  return `import { describe, it, expect } from 'vitest';\n\n` +
    `// Contract test scaffold for spec "${specId}".\n` +
    `// TODO: Replace placeholders with real API/service calls and assertions.\n` +
    `describe('contract:${specId}', () => {\n` +
    `  it.each([\n` +
    `${rows}\n` +
    `  ])('validates %s', (_acId, _criterion) => {\n` +
    `    // TODO: Arrange request/input and invoke the target boundary.\n` +
    `    // TODO: Assert status, schema, and side effects for this AC.\n` +
    `    expect(true).toBe(true);\n` +
    `  });\n` +
    `});\n`;
}

function buildRegressionTestContent(specId: string, criteria: string[]): string {
  const rows = criteria
    .map((criterion, index) => `    ['AC-${index + 1}', ${JSON.stringify(criterion)}],`)
    .join('\n');

  return `import { describe, it, expect } from 'vitest';\n\n` +
    `// Regression test scaffold for spec "${specId}".\n` +
    `// TODO: Capture bug reproductions or golden cases tied to each AC.\n` +
    `describe('regression:${specId}', () => {\n` +
    `  it.each([\n` +
    `${rows}\n` +
    `  ])('prevents regressions for %s', (_acId, _criterion) => {\n` +
    `    // TODO: Reproduce prior failure or execute fixed scenario.\n` +
    `    // TODO: Assert that current behavior stays stable.\n` +
    `    expect(true).toBe(true);\n` +
    `  });\n` +
    `});\n`;
}

function ensureWritable(filePath: string, overwrite: boolean) {
  if (!overwrite && existsSync(filePath)) {
    throw new Error(`Output file already exists: ${filePath} (use --overwrite to replace)`);
  }
}

export function createScaffoldFiles(
  markdown: string,
  specId: string,
  generationOptions: ScaffoldGenerationOptions = {},
): FileEntry[] {
  const criteria = extractAcceptanceCriteria(markdown);
  if (criteria.length === 0) {
    throw new Error('No acceptance criteria bullets found in input document');
  }

  const includeProperty = generationOptions.property !== false;
  const includeContract = generationOptions.contract !== false;
  const includeRegression = generationOptions.regression !== false;

  const files: FileEntry[] = [
    {
      relativePath: path.join('bdd', `${specId}.feature`),
      content: buildFeatureContent(specId, criteria),
    },
    {
      relativePath: `${specId}.acceptance.md`,
      content: buildAcceptanceMapContent(specId, criteria),
    },
  ];

  if (includeProperty) {
    files.push({
      relativePath: path.join('property', `${specId}.property.test.ts`),
      content: buildPropertyTestContent(specId),
    });
  }

  if (includeContract) {
    files.push({
      relativePath: path.join('contract', `${specId}.contract.test.ts`),
      content: buildContractTestContent(specId, criteria),
    });
  }

  if (includeRegression) {
    files.push({
      relativePath: path.join('regression', `${specId}.regression.test.ts`),
      content: buildRegressionTestContent(specId, criteria),
    });
  }

  return files;
}

export function testsScaffold(options: TestsScaffoldOptions) {
  if (!options.input) {
    throw new Error('Missing required option: --input <file>');
  }

  const inputPath = path.resolve(options.input);
  const markdown = readFileSync(inputPath, 'utf8');
  const specId = deriveSpecId(inputPath, options.specId);
  const outputDir = path.resolve(options.out || path.join('tests', 'generated', 'spec-kit', specId));
  const includeProperty = options.property !== false;
  const includeContract = options.contract !== false;
  const includeRegression = options.regression !== false;
  const overwrite = options.overwrite === true;

  const files = createScaffoldFiles(markdown, specId, {
    property: includeProperty,
    contract: includeContract,
    regression: includeRegression,
  });
  mkdirSync(outputDir, { recursive: true });

  for (const file of files) {
    const targetPath = path.join(outputDir, file.relativePath);
    mkdirSync(path.dirname(targetPath), { recursive: true });
    ensureWritable(targetPath, overwrite);
    writeFileSync(targetPath, file.content, 'utf8');
  }

  console.log(`✅ Generated ${files.length} scaffold file(s) in ${outputDir}`);
  for (const file of files) {
    console.log(` - ${file.relativePath}`);
  }
}

export function handleTestsScaffold(options: TestsScaffoldOptions) {
  try {
    testsScaffold(options);
  } catch (error: unknown) {
    const message = error instanceof Error ? error.message : 'Unknown error';
    console.error(`❌ ${message}`);
    safeExit(1);
  }
}
