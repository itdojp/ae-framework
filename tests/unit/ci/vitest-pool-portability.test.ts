import { describe, expect, it } from 'vitest';
import { selectCiPool } from '../../../configs/vitest.config.js';

describe('Vitest CI pool portability', () => {
  it('keeps the reviewed unit thread pool on Windows', () => {
    expect(selectCiPool('win32', 'threads')).toBe('threads');
  });

  it('keeps fork isolation for Windows projects configured for forks', () => {
    expect(selectCiPool('win32', 'forks')).toBe('forks');
  });

  it('keeps fork isolation for non-Windows CI projects', () => {
    expect(selectCiPool('linux', 'threads')).toBe('forks');
  });
});
