/**
 * Default Conformance Rules for the Encrypted Chat specification.
 */

import type { ConformanceRule, ConformanceRuleCategory, ViolationSeverity } from './types.js';

interface RuleTemplate {
  id: string;
  name: string;
  description: string;
  category: ConformanceRuleCategory;
  severity: ViolationSeverity;
  expression: string;
  variables?: string[];
  constraints?: Record<string, unknown>;
  actions?: ConformanceRule['actions'];
  tags?: string[];
}

const ENCRYPTED_CHAT_RULE_TEMPLATES: RuleTemplate[] = [
  {
    id: '4e2be308-9326-43d6-9b69-631b7b6ccfa0',
    name: 'Messages use AES-256-GCM encryption',
    description: 'Ensures outbound messages are encrypted with AES-256-GCM as mandated by BR-SEC-001.',
    category: 'security_policy',
    severity: 'critical',
    expression: 'data.message?.encryption === "AES-256-GCM"',
    variables: ['message.encryption'],
    tags: ['encrypted-chat', 'security', 'aes-256-gcm']
  },
  {
    id: '6ec10de6-9b98-4132-8bd0-28f361c274bf',
    name: 'Auth tag has expected length',
    description: 'Validates that AES-GCM authentication tags are 16 bytes (24 base64 characters).',
    category: 'security_policy',
    severity: 'major',
    expression:
      'validators.isString(data.message?.authTag) && data.message.authTag.length === 24 && /^[A-Za-z0-9+/=]+$/.test(data.message.authTag)',
    variables: ['message.authTag'],
    tags: ['encrypted-chat', 'security', 'auth-tag']
  },
  {
    id: '934d8516-d309-4916-982c-5361634cabfa',
    name: 'Published one-time pre-keys meet threshold',
    description: 'Device registrations must expose at least 100 one-time pre-keys (BR-SEC-002).',
    category: 'security_policy',
    severity: 'major',
    expression: 'Number(data.metrics?.oneTimePreKeyCount ?? 0) >= 100',
    variables: ['metrics.oneTimePreKeyCount'],
    tags: ['encrypted-chat', 'security', 'pre-keys']
  },
  {
    id: '0db0bc0e-5b5d-47cf-8bf3-45dc13f3467c',
    name: 'User retains an active device',
    description: 'Every user must maintain at least one active device entry (BR-USER-001).',
    category: 'business_logic',
    severity: 'major',
    expression: 'Number(data.metrics?.activeDeviceCount ?? 0) >= 1',
    variables: ['metrics.activeDeviceCount'],
    tags: ['encrypted-chat', 'business-rule', 'devices']
  },
  {
    id: '9c8a5f6a-5d0a-4979-8d28-9d603f0d53e2',
    name: 'Active sessions have chain keys and active devices',
    description: 'Active sessions must retain chain keys and both devices must remain reachable (BR-SESSION-001 / INV-001).',
    category: 'state_invariant',
    severity: 'major',
    expression:
      'data.session?.state !== "active" || (Boolean(data.session?.devicesActive) && Number(data.session?.chainKeys?.length ?? 0) >= 1)',
    variables: ['session.state', 'session.chainKeys', 'session.devicesActive'],
    tags: ['encrypted-chat', 'state', 'session']
  },
  {
    id: '6bb8fd9b-cfbc-4513-9f9a-ec7f96462e19',
    name: 'Session rotation thresholds respected',
    description: 'Sessions rotate before 100 messages or 24 hours (BR-PFS-001).',
    category: 'behavioral_constraint',
    severity: 'major',
    expression:
      'Number(data.session?.messagesSinceRotation ?? 0) < 100 && Number(data.session?.hoursSinceRotation ?? 0) < 24',
    variables: ['session.messagesSinceRotation', 'session.hoursSinceRotation'],
    tags: ['encrypted-chat', 'forward-secrecy']
  },
  {
    id: '5593d8e7-156e-4cf6-abbe-3577ab049999',
    name: 'Audit log is append-only',
    description: 'Audit log entries may not be mutated once written (BR-AUD-001).',
    category: 'compliance_rule',
    severity: 'major',
    expression: 'Boolean(data.audit?.appendOnly)',
    variables: ['audit.appendOnly'],
    tags: ['encrypted-chat', 'audit']
  },
  {
    id: '5d7c9b71-3d4c-4a2f-87e4-7ba291eb97d6',
    name: 'Audit payload matches stored event type',
    description: 'Audit payloads must echo their event type (BR-AUD-002).',
    category: 'compliance_rule',
    severity: 'major',
    expression: 'Boolean(data.audit?.payloadAligned)',
    variables: ['audit.payloadAligned'],
    tags: ['encrypted-chat', 'audit', 'payload']
  },
  {
    id: 'ec8b0f84-d27c-4beb-8d98-2195cecf5538',
    name: 'Message delivery latency meets SLA',
    description: 'End-to-end delivery completes within 500ms in-region.',
    category: 'performance_constraint',
    severity: 'minor',
    expression: 'Number(data.metrics?.deliveryLatencyMs ?? 0) <= 500',
    variables: ['metrics.deliveryLatencyMs'],
    tags: ['encrypted-chat', 'latency']
  },
  {
    id: '7f92b6f1-0a4b-49c5-ae33-ec02b53da4e2',
    name: 'GDPR retention window satisfied',
    description: 'Encrypted chat data retains audit logs for 180 days minimum.',
    category: 'compliance_rule',
    severity: 'major',
    expression: 'Number(data.metrics?.gdprRetentionDays ?? 0) >= 180',
    variables: ['metrics.gdprRetentionDays'],
    tags: ['encrypted-chat', 'compliance', 'gdpr']
  },
  {
    id: 'd36d6617-0bab-4829-b187-50a2046137fa',
    name: 'Invalid auth tags emit audit events',
    description: 'Failed authentication tags must surface as message_failed audit entries (BR-MSG-001).',
    category: 'security_policy',
    severity: 'major',
    expression: 'Boolean(data.metrics?.invalidAuthTagLogged)',
    variables: ['metrics.invalidAuthTagLogged'],
    tags: ['encrypted-chat', 'security', 'audit']
  }
];

export function createEncryptedChatDefaultRules(now = new Date().toISOString()): ConformanceRule[] {
  return ENCRYPTED_CHAT_RULE_TEMPLATES.map((template) => ({
    id: template.id,
    name: template.name,
    description: template.description,
    category: template.category,
    severity: template.severity,
    enabled: true,
    condition: {
      expression: template.expression,
      variables: template.variables ?? [],
      constraints: template.constraints ?? {}
    },
    actions: template.actions ?? ['log_violation'],
    metadata: {
      createdAt: now,
      updatedAt: now,
      version: '2.2.0',
      tags: template.tags ?? [],
      owner: 'runtime-conformance'
    }
  }));
}

