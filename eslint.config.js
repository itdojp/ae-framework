// eslint v9 flat (type-checked, soft landing)
import js from '@eslint/js';
import ts from 'typescript-eslint';

export default ts.config(
  {
    ignores: ['dist/**','artifacts/**','node_modules/**','apps/**','packages/**'],
  },
  js.configs.recommended,
  ...ts.configs.recommended,
  {
    files: ['src/**/*.ts'],
    extends: [...ts.configs.recommendedTypeChecked],
    languageOptions: {
      parserOptions: {
        project: ['./tsconfig.verify.json'],
        tsconfigRootDir: import.meta.dirname,
      },
    },
    rules: {
      // 可視化重視：まずは warn から入り、後続PRで error に上げる
      '@typescript-eslint/no-explicit-any': 'warn',
      '@typescript-eslint/no-unsafe-assignment': 'warn',
      '@typescript-eslint/no-unsafe-call': 'warn',
      '@typescript-eslint/no-unsafe-member-access': 'warn',
      '@typescript-eslint/no-unsafe-return': 'warn',
      '@typescript-eslint/restrict-template-expressions': ['warn', { allowNumber: true, allowBoolean: true }],
      '@typescript-eslint/no-floating-promises': 'warn',
      '@typescript-eslint/no-misused-promises': 'warn',
      // Enforce ts-comment policy
      '@typescript-eslint/ban-ts-comment': ['error', {
        'ts-ignore': true,           // completely banned
        'ts-nocheck': true,          // completely banned
        'ts-check': false,
        'ts-expect-error': 'allow-with-description', // description required
        minimumDescriptionLength: 12
      }],
    }
  },
  {
    files: ['src/providers/**/*.ts'],
    languageOptions: {
      parserOptions: {
        project: true,
      },
    },
    rules: {
      '@typescript-eslint/no-unsafe-assignment': 'error',
      '@typescript-eslint/no-unsafe-member-access': 'error',
      '@typescript-eslint/no-unsafe-return': 'error',
    }
  }
);