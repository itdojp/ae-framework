import type { PortMapping } from './container-engine.js';

export interface ExecErrorLike {
  message: string;
  stdout?: string;
  stderr?: string;
  code?: number;
}

const SIZE_UNITS: Record<string, number> = {
  B: 1,
  kB: 1000,
  MB: 1000000,
  GB: 1000000000,
  TB: 1000000000000,
  KiB: 1024,
  MiB: 1024 ** 2,
  GiB: 1024 ** 3,
  TiB: 1024 ** 4
};

function asRecord(value: unknown): Record<string, unknown> | null {
  if (typeof value === 'object' && value !== null) {
    return value as Record<string, unknown>;
  }
  return null;
}

function asString(value: unknown): string | undefined {
  return typeof value === 'string' ? value : undefined;
}

function asNumber(value: unknown): number | undefined {
  return typeof value === 'number' ? value : undefined;
}

export function toExecErrorLike(error: unknown): ExecErrorLike {
  const buildResult = (
    message: string,
    stdout: string | undefined,
    stderr: string | undefined,
    code: number | undefined
  ): ExecErrorLike => {
    const result: ExecErrorLike = { message };
    if (stdout !== undefined) result.stdout = stdout;
    if (stderr !== undefined) result.stderr = stderr;
    if (code !== undefined) result.code = code;
    return result;
  };

  if (error instanceof Error) {
    const record = asRecord(error);
    return buildResult(
      error.message,
      asString(record?.['stdout']),
      asString(record?.['stderr']),
      asNumber(record?.['code'])
    );
  }

  const record = asRecord(error);
  const message =
    asString(record?.['message']) ??
    (typeof error === 'string' ? error : 'Unknown error');

  return buildResult(
    message,
    asString(record?.['stdout']),
    asString(record?.['stderr']),
    asNumber(record?.['code'])
  );
}

export function parseJsonLines<T>(rawOutput: string): T[] {
  return rawOutput
    .trim()
    .split('\n')
    .filter(line => line.trim().length > 0)
    .map((line, index) => {
      try {
        return JSON.parse(line) as T;
      } catch (error) {
        const details = error instanceof Error ? ` (${error.message})` : '';
        throw new Error(`Failed to parse JSON on line ${index + 1}: ${line}${details}`);
      }
    });
}

export function parsePublishedPorts(portsString: string): PortMapping[] {
  if (!portsString) return [];

  const parsedPorts: PortMapping[] = [];
  for (const portMapping of portsString.split(', ')) {
    const match = portMapping.match(/(.+?):(\d+)->(\d+)\/(.+)/);
    if (!match) continue;

    const hostIp = match[1] ?? '';
    const hostPortStr = match[2] ?? '0';
    const containerPortStr = match[3] ?? '0';
    const protocol = match[4] ?? 'tcp';

    parsedPorts.push({
      hostIp,
      hostPort: parseInt(hostPortStr, 10),
      containerPort: parseInt(containerPortStr, 10),
      protocol
    });
  }

  return parsedPorts;
}

export function splitUsagePair(
  usageValue: string | undefined,
  fallbackValue: string = '0 B'
): [string, string] {
  if (!usageValue) return [fallbackValue, fallbackValue];
  const [leftRaw, rightRaw] = usageValue.split('/');
  const left = leftRaw?.trim();
  const right = rightRaw?.trim();
  return [left || fallbackValue, right || fallbackValue];
}

export function parseHumanSizeToBytes(sizeStr: string | undefined): number {
  if (!sizeStr) return 0;
  const match = sizeStr.trim().match(/^(\d+(?:\.\d+)?)\s*([A-Za-z]+)$/);
  if (!match) return 0;

  const value = parseFloat(match[1] ?? '0');
  const unit = match[2] ?? 'B';
  const multiplier = SIZE_UNITS[unit] || 1;

  return Math.round(value * multiplier);
}
