import { describe, expect, it } from 'vitest';

import {
  parseHumanSizeToBytes,
  parseJsonLines,
  parsePublishedPorts,
  splitUsagePair,
  toExecErrorLike
} from '../../../src/services/container/container-engine-utils.js';

describe('container-engine utils', () => {
  it('parseJsonLines parses JSONL payload', () => {
    const parsed = parseJsonLines<{ id: string }>('{"id":"a"}\n{"id":"b"}\n');
    expect(parsed).toEqual([{ id: 'a' }, { id: 'b' }]);
  });

  it('parseJsonLines reports line context for invalid JSON', () => {
    expect(() => parseJsonLines('{"id":"a"}\nnot-json\n')).toThrow(
      /Failed to parse JSON on line 2/
    );
  });

  it('parsePublishedPorts preserves parsed protocol string', () => {
    const parsed = parsePublishedPorts('0.0.0.0:8080->80/tcp, :::8443->443/sctp');
    expect(parsed).toEqual([
      { hostIp: '0.0.0.0', hostPort: 8080, containerPort: 80, protocol: 'tcp' },
      { hostIp: '::', hostPort: 8443, containerPort: 443, protocol: 'sctp' }
    ]);
  });

  it('splitUsagePair returns defaults when format is missing', () => {
    expect(splitUsagePair(undefined)).toEqual(['0 B', '0 B']);
    expect(splitUsagePair('12.3MB')).toEqual(['12.3MB', '0 B']);
    expect(splitUsagePair('12.3MB / 45.0MB')).toEqual(['12.3MB', '45.0MB']);
  });

  it('parseHumanSizeToBytes handles undefined and known units', () => {
    expect(parseHumanSizeToBytes(undefined)).toBe(0);
    expect(parseHumanSizeToBytes('1.5kB')).toBe(1500);
    expect(parseHumanSizeToBytes('2 MiB')).toBe(2 * 1024 * 1024);
  });

  it('toExecErrorLike extracts execution metadata safely', () => {
    const errorWithFields = new Error('failed') as Error & {
      stdout?: string;
      stderr?: string;
      code?: number;
    };
    errorWithFields.stdout = 'out';
    errorWithFields.stderr = 'err';
    errorWithFields.code = 5;

    expect(toExecErrorLike(errorWithFields)).toEqual({
      message: 'failed',
      stdout: 'out',
      stderr: 'err',
      code: 5
    });
    expect(toExecErrorLike('oops')).toEqual({ message: 'oops' });
  });
});
