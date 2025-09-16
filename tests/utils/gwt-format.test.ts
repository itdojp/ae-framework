import { describe, it, expect } from 'vitest';
import { formatGWT } from './gwt-format';

describe('Utils: GWT formatter', () => {
  it('formats Given/When/Then into a single line', () => {
    const s = formatGWT('state initialized', 'action executed', 'result observed');
    expect(s).toBe('Given state initialized | When action executed | Then result observed');
  });
});

