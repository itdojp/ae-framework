import { spawnSync } from 'node:child_process';
import process from 'node:process';

export function resolveToolInvocation(command, args = []) {
  const normalizedCommand = String(command);
  if (/\.[cm]?js$/iu.test(normalizedCommand)) {
    return {
      command: process.execPath,
      args: [normalizedCommand, ...args],
    };
  }
  return { command: normalizedCommand, args };
}

export function spawnToolSync(command, args = [], options = {}) {
  const invocation = resolveToolInvocation(command, args);
  return spawnSync(invocation.command, invocation.args, options);
}
