#!/usr/bin/env node

const KNOWN_PROFILES = ['conservative', 'balanced', 'aggressive'];

const PROFILE_PRESETS = {
  conservative: {
    AE_COPILOT_AUTO_FIX: '1',
    AE_COPILOT_AUTO_FIX_SCOPE: 'docs',
    AE_COPILOT_AUTO_FIX_LABEL: 'copilot-auto-fix',
    AE_AUTO_MERGE: '1',
    AE_AUTO_MERGE_MODE: 'label',
    AE_AUTO_MERGE_LABEL: 'auto-merge',
    AE_GH_THROTTLE_MS: '400',
    AE_GH_RETRY_MAX_ATTEMPTS: '10',
    AE_GH_RETRY_INITIAL_DELAY_MS: '1000',
    AE_GH_RETRY_MAX_DELAY_MS: '120000',
    COPILOT_REVIEW_WAIT_MINUTES: '7',
    COPILOT_REVIEW_MAX_ATTEMPTS: '4',
  },
  balanced: {
    AE_COPILOT_AUTO_FIX: '1',
    AE_COPILOT_AUTO_FIX_SCOPE: 'docs',
    AE_COPILOT_AUTO_FIX_LABEL: '',
    AE_AUTO_MERGE: '1',
    AE_AUTO_MERGE_MODE: 'label',
    AE_AUTO_MERGE_LABEL: 'auto-merge',
    AE_GH_THROTTLE_MS: '300',
    AE_GH_RETRY_MAX_ATTEMPTS: '8',
    AE_GH_RETRY_INITIAL_DELAY_MS: '750',
    AE_GH_RETRY_MAX_DELAY_MS: '60000',
    COPILOT_REVIEW_WAIT_MINUTES: '5',
    COPILOT_REVIEW_MAX_ATTEMPTS: '3',
  },
  aggressive: {
    AE_COPILOT_AUTO_FIX: '1',
    AE_COPILOT_AUTO_FIX_SCOPE: 'all',
    AE_COPILOT_AUTO_FIX_LABEL: '',
    AE_AUTO_MERGE: '1',
    AE_AUTO_MERGE_MODE: 'all',
    AE_AUTO_MERGE_LABEL: '',
    AE_GH_THROTTLE_MS: '150',
    AE_GH_RETRY_MAX_ATTEMPTS: '6',
    AE_GH_RETRY_INITIAL_DELAY_MS: '500',
    AE_GH_RETRY_MAX_DELAY_MS: '30000',
    COPILOT_REVIEW_WAIT_MINUTES: '2',
    COPILOT_REVIEW_MAX_ATTEMPTS: '2',
  },
};

const FIELD_SPECS = [
  { key: 'AE_COPILOT_AUTO_FIX', type: 'toggle', defaultValue: '0' },
  { key: 'AE_COPILOT_AUTO_FIX_SCOPE', type: 'enum', values: ['docs', 'all'], defaultValue: 'docs' },
  { key: 'AE_COPILOT_AUTO_FIX_LABEL', type: 'string', defaultValue: '' },
  { key: 'AE_AUTO_MERGE', type: 'toggle', defaultValue: '0' },
  { key: 'AE_AUTO_MERGE_MODE', type: 'enum', values: ['all', 'label'], defaultValue: 'all' },
  { key: 'AE_AUTO_MERGE_LABEL', type: 'string', defaultValue: '' },
  { key: 'AE_GH_THROTTLE_MS', type: 'int', min: 0, defaultValue: '250' },
  { key: 'AE_GH_RETRY_MAX_ATTEMPTS', type: 'int', min: 1, defaultValue: '8' },
  { key: 'AE_GH_RETRY_INITIAL_DELAY_MS', type: 'int', min: 0, defaultValue: '750' },
  { key: 'AE_GH_RETRY_MAX_DELAY_MS', type: 'int', min: 0, defaultValue: '60000' },
  { key: 'AE_GH_RETRY_DEBUG', type: 'toggle', defaultValue: '0' },
  { key: 'COPILOT_REVIEW_WAIT_MINUTES', type: 'int', min: 0, defaultValue: '5' },
  { key: 'COPILOT_REVIEW_MAX_ATTEMPTS', type: 'int', min: 1, defaultValue: '3' },
];

function normalizeToggle(value) {
  const raw = String(value ?? '').trim().toLowerCase();
  if (raw === '1' || raw === 'true' || raw === 'yes' || raw === 'on') {
    return { valid: true, value: '1' };
  }
  if (raw === '0' || raw === 'false' || raw === 'no' || raw === 'off') {
    return { valid: true, value: '0' };
  }
  return { valid: false, value: null };
}

function normalizeInt(value, min = Number.MIN_SAFE_INTEGER) {
  const raw = String(value ?? '').trim();
  if (!/^-?[0-9]+$/.test(raw)) {
    return { valid: false, value: null };
  }
  const parsed = Number.parseInt(raw, 10);
  if (!Number.isFinite(parsed) || parsed < min) {
    return { valid: false, value: null };
  }
  return { valid: true, value: String(parsed) };
}

function normalizeField(field, value) {
  if (field.type === 'toggle') {
    return normalizeToggle(value);
  }
  if (field.type === 'int') {
    return normalizeInt(value, field.min ?? Number.MIN_SAFE_INTEGER);
  }
  if (field.type === 'enum') {
    const raw = String(value ?? '').trim();
    if (field.values.includes(raw)) {
      return { valid: true, value: raw };
    }
    return { valid: false, value: null };
  }
  return { valid: true, value: String(value ?? '').trim() };
}

function hasExplicitValue(env, key) {
  if (!Object.prototype.hasOwnProperty.call(env, key)) {
    return false;
  }
  return String(env[key] ?? '').trim() !== '';
}

function resolveProfile(rawProfile) {
  const value = String(rawProfile ?? '').trim().toLowerCase();
  if (!value) {
    return { requested: '', resolved: '', source: 'default', warning: null };
  }
  if (KNOWN_PROFILES.includes(value)) {
    return { requested: value, resolved: value, source: 'explicit', warning: null };
  }
  return {
    requested: value,
    resolved: '',
    source: 'default',
    warning: `AE_AUTOMATION_PROFILE=${value} is invalid; expected one of ${KNOWN_PROFILES.join(', ')}`,
  };
}

function resolveAutomationConfig(env = process.env) {
  const warnings = [];
  const profileState = resolveProfile(env.AE_AUTOMATION_PROFILE);
  if (profileState.warning) {
    warnings.push(profileState.warning);
  }

  const profilePreset = profileState.resolved ? PROFILE_PRESETS[profileState.resolved] : null;
  const values = {};
  const sources = {};

  for (const field of FIELD_SPECS) {
    const key = field.key;
    const explicit = hasExplicitValue(env, key) ? String(env[key]).trim() : null;
    if (explicit !== null) {
      const normalized = normalizeField(field, explicit);
      if (normalized.valid) {
        values[key] = normalized.value;
        sources[key] = 'explicit';
        continue;
      }
      warnings.push(`${key}=${explicit} is invalid; falling back.`);
    }

    if (profilePreset && Object.prototype.hasOwnProperty.call(profilePreset, key)) {
      const candidate = profilePreset[key];
      const normalized = normalizeField(field, candidate);
      if (normalized.valid) {
        values[key] = normalized.value;
        sources[key] = 'profile';
        continue;
      }
      warnings.push(`profile ${profileState.resolved} has invalid ${key}=${candidate}; falling back.`);
    }

    const normalizedDefault = normalizeField(field, field.defaultValue);
    values[key] = normalizedDefault.valid ? normalizedDefault.value : '';
    sources[key] = 'default';
  }

  if (values.AE_AUTO_MERGE_MODE === 'label' && !values.AE_AUTO_MERGE_LABEL) {
    warnings.push('AE_AUTO_MERGE_MODE=label requires AE_AUTO_MERGE_LABEL to be non-empty.');
  }

  const initialDelay = Number.parseInt(values.AE_GH_RETRY_INITIAL_DELAY_MS || '0', 10);
  const maxDelay = Number.parseInt(values.AE_GH_RETRY_MAX_DELAY_MS || '0', 10);
  if (Number.isFinite(initialDelay) && Number.isFinite(maxDelay) && maxDelay < initialDelay) {
    values.AE_GH_RETRY_MAX_DELAY_MS = values.AE_GH_RETRY_INITIAL_DELAY_MS;
    sources.AE_GH_RETRY_MAX_DELAY_MS = `${sources.AE_GH_RETRY_MAX_DELAY_MS}+adjusted`;
    warnings.push('AE_GH_RETRY_MAX_DELAY_MS was smaller than AE_GH_RETRY_INITIAL_DELAY_MS; adjusted to match initial delay.');
  }

  return {
    profile: profileState,
    values,
    sources,
    warnings,
  };
}

function toGithubEnv(config) {
  const lines = [
    `AE_AUTOMATION_PROFILE_RESOLVED=${config.profile.resolved}`,
    `AE_AUTOMATION_PROFILE_SOURCE=${config.profile.source}`,
  ];
  for (const field of FIELD_SPECS) {
    lines.push(`${field.key}=${config.values[field.key] ?? ''}`);
  }
  return `${lines.join('\n')}\n`;
}

function toSummaryMarkdown(config) {
  const lines = [
    '### Automation Config',
    `- requested profile: ${config.profile.requested || '(none)'}`,
    `- resolved profile: ${config.profile.resolved || '(none)'}`,
    '| Key | Value | Source |',
    '| --- | --- | --- |',
  ];
  for (const field of FIELD_SPECS) {
    const key = field.key;
    lines.push(`| ${key} | ${config.values[key] ?? ''} | ${config.sources[key] ?? 'unknown'} |`);
  }
  if (config.warnings.length > 0) {
    lines.push('', 'Warnings:');
    for (const warning of config.warnings) {
      lines.push(`- ${warning}`);
    }
  }
  return `${lines.join('\n')}\n`;
}

function parseArgs(argv) {
  const options = {
    format: 'json',
    strict: false,
  };

  for (let i = 2; i < argv.length; i += 1) {
    const current = argv[i];
    if ((current === '--format' || current === '-f') && argv[i + 1]) {
      options.format = String(argv[++i]).trim();
    } else if (current === '--strict') {
      options.strict = true;
    }
  }

  return options;
}

function main() {
  const options = parseArgs(process.argv);
  const config = resolveAutomationConfig(process.env);

  if (options.format === 'github-env') {
    process.stdout.write(toGithubEnv(config));
  } else if (options.format === 'summary') {
    process.stdout.write(toSummaryMarkdown(config));
  } else {
    process.stdout.write(`${JSON.stringify(config, null, 2)}\n`);
  }

  if (options.strict && config.warnings.length > 0) {
    process.exitCode = 1;
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export {
  KNOWN_PROFILES,
  PROFILE_PRESETS,
  resolveAutomationConfig,
  toGithubEnv,
  toSummaryMarkdown,
};
