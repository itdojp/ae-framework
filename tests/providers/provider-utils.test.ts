import { describe, expect, test } from 'vitest';
import {
  stringifyUnknown,
  extractAnthropicText,
  extractGeminiText,
  hasConstructorProperty,
} from '../../src/providers/provider-utils.js';

describe('provider-utils', () => {
  describe('stringifyUnknown', () => {
    test('returns empty string for nullish values', () => {
      expect(stringifyUnknown(null)).toBe('');
      expect(stringifyUnknown(undefined)).toBe('');
    });

    test('returns string values as-is', () => {
      expect(stringifyUnknown('hello')).toBe('hello');
    });

    test('stringifies numbers and booleans', () => {
      expect(stringifyUnknown(42)).toBe('42');
      expect(stringifyUnknown(true)).toBe('true');
    });

    test('extracts message from Error instances', () => {
      expect(stringifyUnknown(new Error('boom'))).toBe('boom');
    });

    test('serializes objects when possible', () => {
      expect(stringifyUnknown({ ok: true })).toBe('{"ok":true}');
    });

    test('uses fallback when serialization fails', () => {
      const circular: { self?: unknown } = {};
      circular.self = circular;
      expect(stringifyUnknown(circular, 'fallback')).toBe('fallback');
    });
  });

  describe('extractAnthropicText', () => {
    test('returns text from a string response', () => {
      expect(extractAnthropicText('hi')).toBe('hi');
    });

    test('returns text from an object with text field', () => {
      expect(extractAnthropicText({ text: 'from field' })).toBe('from field');
    });

    test('returns first non-empty entry from arrays', () => {
      const content = [{ text: '' }, { text: 'first' }, { text: 'second' }];
      expect(extractAnthropicText(content)).toBe('first');
    });

    test('returns empty string when no text is found', () => {
      expect(extractAnthropicText({})).toBe('');
    });
  });

  describe('extractGeminiText', () => {
    test('uses text() method when present', () => {
      const response = { text: () => 'from method' };
      expect(extractGeminiText(response)).toBe('from method');
    });

    test('stringifies non-string text() values', () => {
      const response = { text: () => 123 };
      expect(extractGeminiText(response)).toBe('123');
    });

    test('extracts from candidates/parts shape', () => {
      const response = {
        candidates: [
          {
            content: {
              parts: [{ text: 'from parts' }],
            },
          },
        ],
      };
      expect(extractGeminiText(response)).toBe('from parts');
    });

    test('returns empty string when no text is available', () => {
      expect(extractGeminiText({})).toBe('');
    });
  });

  describe('hasConstructorProperty', () => {
    test('returns true for constructor functions', () => {
      const mod = { default: class Example {} };
      expect(hasConstructorProperty(mod, 'default')).toBe(true);
    });

    test('returns false for non-function values', () => {
      const mod = { default: 'not a constructor' };
      expect(hasConstructorProperty(mod, 'default')).toBe(false);
    });

    test('returns false for non-object inputs', () => {
      expect(hasConstructorProperty(null, 'default')).toBe(false);
    });
  });
});
