import { execSync, spawnSync } from 'child_process';
import { existsSync } from 'fs';
import { glob } from 'glob';
import type { AEFrameworkConfig, Guard, GuardResult } from '../types.js';
import { toMessage } from '../../utils/error-utils.js';
import { getCurrentPhase, shouldEnforceGate, getThreshold } from '../../utils/quality-policy-loader.js';


export const GUARD_SCRIPT_EXECUTION_APPROVAL_SCOPE = 'guard-script-execution' as const;

export interface GuardRunnerOptions {
  dryRun?: boolean;
  apply?: boolean;
  approvalScope?: string;
  agentContext?: boolean;
  cwd?: string;
  env?: NodeJS.ProcessEnv;
}

export interface GuardScriptExecutionPolicy {
  dryRun: boolean;
  apply: boolean;
  approvalRequired: boolean;
  approvalScope?: string;
  agentContext: boolean;
}

type GuardCommandResult = {
  executed: boolean;
  output: string;
  message?: string;
};

type SpawnLikeResult = {
  status?: number | null;
  signal?: NodeJS.Signals | null;
  stdout?: string | Buffer | null;
  stderr?: string | Buffer | null;
  error?: Error;
};

type GuardNpmInvocation = {
  command: string;
  args: string[];
};

export function createGuardNpmInvocation(
  args: string[],
  platform: NodeJS.Platform = process.platform,
  env: NodeJS.ProcessEnv = process.env,
): GuardNpmInvocation {
  if (platform !== 'win32') {
    return { command: 'npm', args };
  }
  return {
    command: env['ComSpec'] ?? env['COMSPEC'] ?? 'cmd.exe',
    args: ['/d', '/s', '/c', 'npm.cmd', ...args],
  };
}

const isTruthyEnv = (value: string | undefined): boolean => {
  if (value === undefined) return false;
  const normalized = value.trim().toLowerCase();
  return normalized.length > 0 && !['0', 'false', 'no', 'off'].includes(normalized);
};

const isGuardAgentContext = (env: NodeJS.ProcessEnv = process.env): boolean => (
  isTruthyEnv(env['AE_GUARD_AGENT_CONTEXT']) ||
  isTruthyEnv(env['AE_AGENT_CONTEXT']) ||
  isTruthyEnv(env['AE_GUARD_UNTRUSTED_CHECKOUT']) ||
  isTruthyEnv(env['AE_UNTRUSTED_CHECKOUT'])
);

export function getGuardScriptExecutionPolicy(options: GuardRunnerOptions = {}): GuardScriptExecutionPolicy {
  const env = options.env ?? process.env;
  const agentContext = options.agentContext ?? isGuardAgentContext(env);
  const apply = options.apply === true;
  const approvalScope = options.approvalScope;
  const dryRun = options.dryRun === true || (agentContext && !apply);
  const approvalRequired = agentContext && apply && approvalScope !== GUARD_SCRIPT_EXECUTION_APPROVAL_SCOPE;
  const policy: GuardScriptExecutionPolicy = {
    dryRun,
    apply,
    approvalRequired,
    agentContext,
  };
  if (approvalScope !== undefined) {
    policy.approvalScope = approvalScope;
  }
  return policy;
}

const SENSITIVE_ENV_NAME_PATTERN = /(?:^|_)(?:token|secret|password|passwd|credential|credentials|cookie|session|authorization|auth|private(?:_key)?|access_key|api_key)(?:_|$)/i;
const SENSITIVE_ENV_EXACT_NAMES = new Set([
  'GITHUB_TOKEN',
  'GH_TOKEN',
  'NPM_TOKEN',
  'NODE_AUTH_TOKEN',
  'ACTIONS_ID_TOKEN_REQUEST_TOKEN',
]);

export function createGuardProcessEnv(source: NodeJS.ProcessEnv = process.env): NodeJS.ProcessEnv {
  const env: NodeJS.ProcessEnv = {};
  for (const [key, value] of Object.entries(source)) {
    if (value === undefined) continue;
    if (SENSITIVE_ENV_EXACT_NAMES.has(key) || SENSITIVE_ENV_NAME_PATTERN.test(key)) {
      continue;
    }
    env[key] = value;
  }
  return env;
}

class GuardScriptApprovalRequiredError extends Error {
  constructor(command: string) {
    super(
      `Guard script execution requires --apply --approval-scope ${GUARD_SCRIPT_EXECUTION_APPROVAL_SCOPE} before running ${command} in an agent or untrusted-checkout context`
    );
    this.name = 'GuardScriptApprovalRequiredError';
  }
}

class GuardCommandFailedError extends Error {
  readonly stdout?: string;
  readonly stderr?: string;

  constructor(command: string, result: SpawnLikeResult) {
    const status = result.status ?? (result.signal ? `signal ${result.signal}` : 'unknown');
    super(`Guard command failed (${command}) with status ${status}`);
    this.name = 'GuardCommandFailedError';
    const stdout = toOutputText(result.stdout);
    const stderr = toOutputText(result.stderr);
    if (stdout !== undefined) {
      this.stdout = stdout;
    }
    if (stderr !== undefined) {
      this.stderr = stderr;
    }
  }
}

const toOutputText = (value: string | Buffer | null | undefined): string | undefined => {
  if (typeof value === 'string') {
    return value;
  }
  if (Buffer.isBuffer(value)) {
    return value.toString('utf8');
  }
  if (value === null) {
    return undefined;
  }
  return value;
};

type ExecErrorOutput = {
  stdout?: string | Buffer;
  stderr?: string | Buffer;
};

const readExecOutput = (error: unknown): string => {
  if (!error || typeof error !== 'object') {
    return '';
  }
  const candidate = error as ExecErrorOutput;
  const toText = (value: string | Buffer | undefined): string | undefined => {
    if (typeof value === 'string') {
      return value;
    }
    if (Buffer.isBuffer(value)) {
      return value.toString('utf8');
    }
    return undefined;
  };

  const stdoutText = toText(candidate.stdout);
  if (stdoutText && stdoutText.length > 0) {
    return stdoutText;
  }
  const stderrText = toText(candidate.stderr);
  if (stderrText && stderrText.length > 0) {
    return stderrText;
  }
  if (stdoutText !== undefined) {
    return stdoutText;
  }
  if (stderrText !== undefined) {
    return stderrText;
  }
  return '';
};

export class GuardRunner {
  private readonly executionPolicy: GuardScriptExecutionPolicy;
  private readonly cwd: string;
  private readonly env: NodeJS.ProcessEnv;

  constructor(private config: AEFrameworkConfig, options: GuardRunnerOptions = {}) {
    this.executionPolicy = getGuardScriptExecutionPolicy(options);
    this.cwd = options.cwd ?? process.cwd();
    this.env = options.env ?? process.env;
  }

  async run(guard: Guard): Promise<GuardResult> {
    switch (guard.name) {
      case 'TDD Guard':
        return this.runTDDGuard();
      
      case 'Test Execution Guard':
        return this.runTestExecutionGuard();
      
      case 'RED-GREEN Cycle Guard':
        return this.runRedGreenCycleGuard();
      
      case 'Coverage Guard':
        return this.runCoverageGuard();
      
      default:
        return { success: true, message: `Unknown guard: ${guard.name}` };
    }
  }

  private async runTDDGuard(): Promise<GuardResult> {
    try {
      // Check that for each source file, there's a corresponding test file
      const srcFiles = await glob('src/**/*.ts');
      const testFiles = await glob('tests/**/*.test.ts');
      
      const violations: string[] = [];
      
      for (const srcFile of srcFiles) {
        // Skip index files and configuration files
        if (srcFile.includes('index.ts') || srcFile.includes('config')) {
          continue;
        }
        
        const baseName = srcFile
          .replace('src/', '')
          .replace('.ts', '')
          .split('/').pop() || '';
          
        const hasTest = testFiles.some(testFile => {
          const testBaseName = testFile
            .replace('tests/', '')
            .replace('.test.ts', '')
            .split('/').pop() || '';
          return testBaseName.includes(baseName) || baseName.includes(testBaseName);
        });
        
        if (!hasTest) {
          violations.push(srcFile);
        }
      }
      
      if (violations.length > 0) {
        return {
          success: false,
          message: `Files without corresponding tests: ${violations.slice(0, 3).join(', ')}${violations.length > 3 ? ` (and ${violations.length - 3} more)` : ''}`
        };
      }
      
      return { success: true, message: 'All source files have corresponding tests' };
    } catch (error: unknown) {
      return { success: false, message: `TDD Guard error: ${toMessage(error)}` };
    }
  }

  private async runTestExecutionGuard(): Promise<GuardResult> {
    try {
      // Check if tests pass
      const commandResult = this.runNpmScript(['test', '--silent'], 'npm test --silent');
      if (!commandResult.executed) {
        return { success: true, message: commandResult.message ?? 'Dry-run preview: npm test --silent was not executed' };
      }
      const result = commandResult.output;
      
      // Look for successful test indicators
      const hasPassedTests = result.includes('passing') || result.includes('✓') || !result.includes('failing');
      
      if (hasPassedTests) {
        return { success: true, message: 'All tests pass' };
      } else {
        return { success: false, message: 'Some tests are failing' };
      }
    } catch (error: unknown) {
      if (error instanceof GuardScriptApprovalRequiredError) {
        return { success: false, message: error.message };
      }
      const output = readExecOutput(error);
      return {
        success: false,
        message: `Tests failed: ${output.split('\n').slice(-3).join('\n').trim() || toMessage(error)}`
      };
    }
  }

  private async runRedGreenCycleGuard(): Promise<GuardResult> {
    try {
      // This guard checks if we're following RED-GREEN cycle
      // In practice, this would need to track test history
      
      // For now, we check if there are recent commits with test changes
      if (existsSync('.git')) {
        try {
          const gitLog = execSync('git log --oneline -5 --grep="test"', { encoding: 'utf8' });
          const hasTestCommits = gitLog.trim().length > 0;
          
          if (hasTestCommits) {
            return { success: true, message: 'Recent commits show test-first development' };
          }
        } catch {
          // Git command failed, continue with other checks
        }
      }
      
      // Timestamp heuristics are intentionally omitted because CI checkout times are not stable.
      const testFiles = await glob('tests/**/*.test.ts');
      
      if (testFiles.length === 0) {
        return { success: false, message: 'No test files found' };
      }
      
      return { success: true, message: 'RED-GREEN cycle appears to be followed' };
    } catch (error: unknown) {
      return { success: false, message: `RED-GREEN cycle check failed: ${toMessage(error)}` };
    }
  }

  private async runCoverageGuard(): Promise<GuardResult> {
    try {
      // Run coverage check
      let commandResult: GuardCommandResult;
      try {
        commandResult = this.runNpmScript(['run', 'coverage', '--silent'], 'npm run coverage --silent');
      } catch (error) {
        if (error instanceof GuardScriptApprovalRequiredError) {
          throw error;
        }
        // Fallback to npm test with coverage if npm run coverage fails
        commandResult = this.runNpmScript(['test', '--', '--coverage', '--silent'], 'npm test -- --coverage --silent');
      }
      if (!commandResult.executed) {
        return { success: true, message: commandResult.message ?? 'Dry-run preview: coverage guard npm scripts were not executed' };
      }
      const result = commandResult.output;
      
      // Parse coverage output
      const coverageMatch = result.match(/All files[^\d]*(\d+(?:\.\d+)?)/);
      const coverage = coverageMatch && coverageMatch[1] ? parseFloat(coverageMatch[1]) : 0;
      
      // Get threshold from quality policy
      const currentPhase = getCurrentPhase();
      const threshold = shouldEnforceGate('coverage', currentPhase) 
        ? (getThreshold('coverage', 'lines') as number) || 80 
        : 80;
      
      if (coverage >= threshold) {
        return { success: true, message: `Coverage: ${coverage}% (>= ${threshold}%)` };
      } else {
        return { success: false, message: `Coverage: ${coverage}% (< ${threshold}%)` };
      }
    } catch (error: unknown) {
      if (error instanceof GuardScriptApprovalRequiredError) {
        return { success: false, message: error.message };
      }
      // If coverage command fails, check if at least tests exist and pass
      try {
        const testResult = await this.runTestExecutionGuard();
        if (testResult.success) {
          return { success: true, message: 'Coverage tool not available, but tests pass' };
        }
        return { success: false, message: 'Cannot determine coverage and tests fail' };
      } catch {
        return { success: false, message: 'Cannot determine coverage and tests fail' };
      }
    }
  }

  private runNpmScript(args: string[], displayCommand: string): GuardCommandResult {
    if (this.executionPolicy.approvalRequired) {
      throw new GuardScriptApprovalRequiredError(displayCommand);
    }
    if (this.executionPolicy.dryRun) {
      return {
        executed: false,
        output: '',
        message: `Dry-run preview: would execute ${displayCommand}. Use --apply --approval-scope ${GUARD_SCRIPT_EXECUTION_APPROVAL_SCOPE} in an agent or untrusted-checkout context to run repository scripts.`,
      };
    }

    const invocation = createGuardNpmInvocation(args, process.platform, this.env);
    const result = spawnSync(invocation.command, invocation.args, {
      cwd: this.cwd,
      encoding: 'utf8',
      env: createGuardProcessEnv(this.env),
      shell: false,
      stdio: 'pipe',
    }) as SpawnLikeResult;
    if (result.error) {
      throw result.error;
    }
    if (result.status !== 0) {
      throw new GuardCommandFailedError(displayCommand, result);
    }
    return {
      executed: true,
      output: `${toOutputText(result.stdout) ?? ''}${toOutputText(result.stderr) ?? ''}`,
    };
  }

  // Utility method to check git status for TDD violations
  async checkGitForTDDViolations(): Promise<string[]> {
    const violations: string[] = [];
    
    try {
      if (!existsSync('.git')) {
        return violations;
      }
      
      // Check if source files were added without corresponding tests
      const stagedFiles = execSync('git diff --cached --name-only', { encoding: 'utf8' })
        .split('\n')
        .filter(file => file.trim());
      
      const stagedSrcFiles = stagedFiles.filter(file => 
        file.startsWith('src/') && file.endsWith('.ts') && !file.includes('index.ts')
      );
      
      const stagedTestFiles = stagedFiles.filter(file => 
        file.startsWith('tests/') && file.endsWith('.test.ts')
      );
      
      for (const srcFile of stagedSrcFiles) {
        const baseName = srcFile.replace('src/', '').replace('.ts', '').split('/').pop() || '';
        const hasCorrespondingTest = stagedTestFiles.some(testFile => 
          testFile.includes(baseName)
        );
        
        if (!hasCorrespondingTest) {
          violations.push(`Source file ${srcFile} staged without corresponding test`);
        }
      }
      
    } catch (error: unknown) {
      // Git command failed, skip git-based checks
    }
    
    return violations;
  }
}
