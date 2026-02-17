import type { Requirement, RequirementSource } from './intent-agent.js';

export function extractRequirementsFromSources(sources: RequirementSource[]): string[] {
  const requirements: string[] = [];
  for (const source of sources) {
    requirements.push(...extractFromSource(source));
  }
  return requirements;
}

export function parseStructuredRequirements(raw: string[]): Requirement[] {
  const normalized = raw
    .map((text) => text.trim())
    .filter((text) => text.length > 0);

  return normalized.map((text, index) => ({
    id: `REQ-${String(index + 1).padStart(3, '0')}`,
    type: determineRequirementType(text),
    category: determineCategory(text),
    description: text,
    priority: determinePriority(text),
    acceptance: [],
    source: 'extracted',
    status: 'draft',
  }));
}

export function determineRequirementType(text: string): Requirement['type'] {
  const lowerText = text.toLowerCase();

  if (
    lowerText.includes('performance')
    || lowerText.includes('security')
    || lowerText.includes('scalability')
    || lowerText.includes('usability')
    || lowerText.includes('reliability')
    || lowerText.includes('availability')
    || lowerText.includes('response time')
    || lowerText.includes('throughput')
  ) {
    return 'non-functional';
  }

  if (
    lowerText.includes('business')
    || lowerText.includes('revenue')
    || lowerText.includes('customer')
    || lowerText.includes('policy')
    || lowerText.includes('compliance')
    || lowerText.includes('regulation')
  ) {
    return 'business';
  }

  if (
    lowerText.includes('api')
    || lowerText.includes('database')
    || lowerText.includes('integration')
    || lowerText.includes('platform')
    || lowerText.includes('architecture')
    || lowerText.includes('framework')
    || lowerText.includes('technology')
  ) {
    return 'technical';
  }

  return 'functional';
}

export function determineCategory(text: string): string {
  const lowerText = text.toLowerCase();

  if (
    containsKeyword(lowerText, [
      'auth',
      'authentication',
      'authenticate',
      'authorization',
      'authorisation',
      'authorize',
      'login',
      'sign-in',
      'signin',
      'oauth',
      'sso',
    ])
  ) {
    return 'authentication';
  }
  if (containsKeyword(lowerText, ['security', 'secure', 'encryption', 'encrypted'])) {
    return 'security';
  }
  if (containsKeyword(lowerText, ['performance', 'latency', 'response time', 'throughput', 'scalability'])) {
    return 'performance';
  }
  if (containsKeyword(lowerText, ['data', 'database', 'storage', 'persistence'])) {
    return 'data-management';
  }
  if (
    containsKeyword(lowerText, ['ui', 'user interface'])
    || containsKeyword(lowerText, ['ux', 'user experience'])
  ) {
    return 'ui';
  }
  if (containsKeyword(lowerText, ['api', 'rest', 'graphql'])) {
    return 'api';
  }

  return 'general';
}

export function determinePriority(text: string): Requirement['priority'] {
  const lowerText = text.toLowerCase();

  const mustPattern = /\b(must|critical)\b/;
  const shouldPattern = /\b(should|important)\b/;
  const couldPattern = /\b(could|nice to have)\b/;
  const wontPattern = /\b(wont|future)\b/;

  if (mustPattern.test(lowerText)) return 'must';
  if (shouldPattern.test(lowerText)) return 'should';
  if (couldPattern.test(lowerText)) return 'could';
  if (wontPattern.test(lowerText)) return 'wont';

  return 'should';
}

function containsKeyword(text: string, keywords: string[]): boolean {
  return keywords.some((keyword) => {
    const escaped = escapeForRegex(keyword);
    return new RegExp(`\\b${escaped}\\b`, 'i').test(text);
  });
}

function escapeForRegex(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function extractFromSource(source: RequirementSource): string[] {
  switch (source.type) {
    case 'text':
      return source.content.split('\n').filter((line) => line.trim());
    case 'document':
      return parseDocument(source.content);
    case 'conversation':
      return extractFromConversation(source.content);
    case 'issue':
      return parseIssue(source.content);
    case 'email':
      return extractFromEmail(source.content);
    case 'diagram':
      return extractFromDiagram(source.content);
    default:
      return [source.content];
  }
}

function parseDocument(content: string): string[] {
  const lines = content.split('\n');
  const requirements: string[] = [];

  for (const line of lines) {
    const trimmedLine = line.trim();
    if (
      trimmedLine.match(
        /^(\d+[\.\)]\s+|[\-\*]\s+|(MUST|SHOULD|MAY|SHALL):\s*|.*(must|should|shall|will)\s+)/i,
      )
    ) {
      const cleanRequirement = trimmedLine
        .replace(/^(\d+[\.\)]\s+|[\-\*]\s+|(MUST|SHOULD|MAY|SHALL):\s*)/i, '')
        .trim();
      if (cleanRequirement.length > 10) {
        requirements.push(cleanRequirement);
      }
    } else if (
      trimmedLine.match(/(requirement|feature|capability|function).*:/i)
      && trimmedLine.length > 15
    ) {
      requirements.push(trimmedLine);
    }
  }

  return requirements;
}

function extractFromConversation(content: string): string[] {
  const requirements: string[] = [];
  const patterns = [
    /I need (.+)/gi,
    /We want (.+)/gi,
    /The system should (.+)/gi,
    /Users must be able to (.+)/gi,
  ];

  for (const pattern of patterns) {
    let match;
    pattern.lastIndex = 0;
    while ((match = pattern.exec(content)) !== null) {
      if (match[1]) {
        requirements.push(match[1]);
      }
    }
  }

  return requirements;
}

function parseIssue(content: string): string[] {
  const requirements: string[] = [];
  const sections = content.split(/#+\s+/);

  for (const section of sections) {
    const lowered = section.toLowerCase();
    if (lowered.includes('requirement') || lowered.includes('acceptance')) {
      requirements.push(section.trim());
    }
  }

  return requirements;
}

function extractFromEmail(content: string): string[] {
  return extractFromConversation(content);
}

function extractFromDiagram(content: string): string[] {
  return [content];
}
