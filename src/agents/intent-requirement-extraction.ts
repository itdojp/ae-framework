import type { Requirement, RequirementSource } from './intent-agent.js';

export function extractRequirementsFromSources(sources: RequirementSource[]): string[] {
  const requirements: string[] = [];
  for (const source of sources) {
    requirements.push(...extractFromSource(source));
  }
  return requirements;
}

export function parseStructuredRequirements(raw: string[]): Requirement[] {
  return raw.map((text, index) => ({
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

  if (lowerText.includes('auth')) return 'authentication';
  if (lowerText.includes('security')) return 'security';
  if (lowerText.includes('performance')) return 'performance';
  if (lowerText.includes('data')) return 'data-management';
  if (lowerText.includes('ui') || lowerText.includes('user interface')) return 'ui';
  if (lowerText.includes('api')) return 'api';

  return 'general';
}

export function determinePriority(text: string): Requirement['priority'] {
  const lowerText = text.toLowerCase();

  if (lowerText.includes('must') || lowerText.includes('critical')) return 'must';
  if (lowerText.includes('should') || lowerText.includes('important')) return 'should';
  if (lowerText.includes('could') || lowerText.includes('nice to have')) return 'could';
  if (lowerText.includes('wont') || lowerText.includes('future')) return 'wont';

  return 'should';
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
