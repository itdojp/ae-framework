export const normalizeProgramArgv = (
  argv: string[],
  env: NodeJS.ProcessEnv = process.env,
): string[] => {
  if (argv.length < 3) {
    return argv;
  }

  const nodePath = argv[0];
  const scriptPath = argv[1];
  if (!nodePath || !scriptPath) {
    return argv;
  }

  const commandArgs = argv.slice(2);
  if (commandArgs[0] === '--') {
    return [nodePath, scriptPath, ...commandArgs.slice(1)];
  }

  // For package script execution (pnpm/npm/yarn), normalize the injected
  // separator that appears before forwarded option arguments.
  if (!env['npm_lifecycle_event']) {
    return argv;
  }

  const separatorIndex = commandArgs.indexOf('--');
  if (separatorIndex < 0) {
    return argv;
  }

  const nextToken = commandArgs[separatorIndex + 1];
  if (!nextToken || !nextToken.startsWith('-')) {
    return argv;
  }

  return [
    nodePath,
    scriptPath,
    ...commandArgs.slice(0, separatorIndex),
    ...commandArgs.slice(separatorIndex + 1),
  ];
};
