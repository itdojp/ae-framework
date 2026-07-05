import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { Command } from 'commander';
import chalk from 'chalk';
import { safeExit } from '../utils/safe-exit.js';

const DEFAULT_ACTION = 'itdojp/ae-framework';
const BUILTIN_PROFILES = new Set(['minimal', 'standard', 'full']);

export interface InitProfileOptions {
  root?: string;
  profile?: string;
  artifactsDir?: string;
  actionRef?: string;
  policy?: string;
  dryRun?: boolean;
  force?: boolean;
}

export interface InitScaffoldFile {
  path: string;
  content: string;
  existed: boolean;
}

export interface InitScaffoldResult {
  root: string;
  profile: string;
  artifactsDir: string;
  actionRef: string;
  dryRun: boolean;
  files: InitScaffoldFile[];
}

function normalizeNonEmpty(value: string | undefined, fallback: string): string {
  const normalized = (value ?? fallback).trim();
  if (!normalized) throw new Error('value must not be empty');
  if (normalized.includes('\n') || normalized.includes('\r')) throw new Error('value must be single-line');
  return normalized;
}

function yamlString(value: string): string {
  return JSON.stringify(value);
}

function workflowContent(options: { profile: string; artifactsDir: string; policy?: string | undefined; actionRef: string }): string {
  const action = `${DEFAULT_ACTION}@${options.actionRef}`;
  const policyLine = options.policy ? `          policy: ${yamlString(options.policy)}\n` : '';
  return `name: ae-framework Assurance Gate

on:
  pull_request:
  workflow_dispatch:

permissions:
  contents: read
  actions: read

jobs:
  assurance:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
        with:
          node-version: "20"
      - uses: ${action}
        with:
          profile: ${yamlString(options.profile)}
          artifacts-dir: ${yamlString(options.artifactsDir)}
${policyLine}`;
}

function configContent(options: { profile: string; artifactsDir: string; policy?: string | undefined; actionRef: string }): string {
  const policyLine = options.policy ? `policy: ${yamlString(options.policy)}\n` : '';
  const profileKind = BUILTIN_PROFILES.has(options.profile) ? 'builtin' : 'custom';
  return `schemaVersion: ae-assurance-init/v1
profile: ${yamlString(options.profile)}
profileKind: ${yamlString(profileKind)}
artifactsDir: ${yamlString(options.artifactsDir)}
action: ${yamlString(`${DEFAULT_ACTION}@${options.actionRef}`)}
${policyLine}`;
}

function assertWritableTarget(root: string, target: string): string {
  const resolved = path.resolve(root, target);
  const relative = path.relative(root, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`target path escapes root: ${target}`);
  }
  return resolved;
}

export function scaffoldAssuranceInit(options: InitProfileOptions = {}): InitScaffoldResult {
  const root = path.resolve(options.root ?? process.cwd());
  const profile = normalizeNonEmpty(options.profile, 'minimal');
  const artifactsDir = normalizeNonEmpty(options.artifactsDir, 'artifacts');
  const actionRef = normalizeNonEmpty(options.actionRef, 'v1');
  const policy = options.policy === undefined ? undefined : normalizeNonEmpty(options.policy, options.policy);
  const workflowPath = assertWritableTarget(root, '.github/workflows/assurance.yml');
  const configPath = assertWritableTarget(root, '.ae/assurance.yml');
  const files: InitScaffoldFile[] = [
    {
      path: workflowPath,
      content: workflowContent({ profile, artifactsDir, policy, actionRef }),
      existed: existsSync(workflowPath),
    },
    {
      path: configPath,
      content: configContent({ profile, artifactsDir, policy, actionRef }),
      existed: existsSync(configPath),
    },
  ];

  const existing = files.filter((file) => file.existed);
  if (existing.length > 0 && options.force !== true) {
    throw new Error(`refusing to overwrite existing files without --force: ${existing.map((file) => path.relative(root, file.path)).join(', ')}`);
  }

  if (options.dryRun !== true) {
    for (const file of files) {
      mkdirSync(path.dirname(file.path), { recursive: true });
      writeFileSync(file.path, file.content);
    }
  }

  return {
    root,
    profile,
    artifactsDir,
    actionRef,
    dryRun: options.dryRun === true,
    files,
  };
}

export function createInitCommand(): Command {
  const command = new Command('init');
  command
    .description('Scaffold deploy-time ae-framework assurance profile adoption')
    .option('--root <path>', 'Target repository root (default: cwd)', process.cwd())
    .option('--profile <nameOrPath>', 'minimal, standard, full, or custom profile YAML path', 'minimal')
    .option('--artifacts-dir <path>', 'Assurance artifacts directory in the target repo', 'artifacts')
    .option('--policy <path>', 'Optional policy YAML path in the target repo')
    .option('--action-ref <ref>', 'ae-framework action ref to use', 'v1')
    .option('--dry-run', 'Print files without writing them')
    .option('--force', 'Overwrite existing scaffold files')
    .action((options: InitProfileOptions) => {
      try {
        const result = scaffoldAssuranceInit(options);
        const verb = result.dryRun ? 'Would write' : 'Wrote';
        console.log(chalk.green(`ae init scaffold prepared for profile ${result.profile}`));
        for (const file of result.files) {
          console.log(`${verb}: ${path.relative(result.root, file.path)}`);
          if (result.dryRun) {
            console.log(file.content.trimEnd());
          }
        }
      } catch (error: unknown) {
        console.error(chalk.red(error instanceof Error ? error.message : String(error)));
        safeExit(1);
      }
    });
  return command;
}
