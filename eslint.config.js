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
      '@typescript-eslint/switch-exhaustiveness-check': 'error',
      // @ts-expect-error policy helper (warns for incomplete format)
      'no-inline-comments': ['off'], // Allow inline comments for ts-expect-error
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
  },
  // T1 escalation (targeted): strengthen unsafe rules for MCP servers
  {
    files: [
      'src/mcp-server/**/*.ts',
    ],
    languageOptions: {
      parserOptions: {
        project: ['./tsconfig.verify.json'],
        tsconfigRootDir: import.meta.dirname,
      },
    },
    rules: {
      // Keep no-explicit-any as warn for now (soft landing),
      // but escalate unsafe operations to error in MCP boundaries
      '@typescript-eslint/no-unsafe-assignment': 'error',
      '@typescript-eslint/no-unsafe-call': 'error',
      '@typescript-eslint/no-unsafe-member-access': 'error',
      '@typescript-eslint/no-unsafe-return': 'error',
      '@typescript-eslint/no-floating-promises': 'error',
      '@typescript-eslint/no-misused-promises': 'error',
    }
  }
  },
  // T1 escalation (file-specific): enforce no-explicit-any in cleaned files
  {
    files: [
      'src/mcp-server/verify-server.ts',
      'src/mcp-server/code-generation-server.ts',
    ],
    languageOptions: {
      parserOptions: {
        project: ['./tsconfig.verify.json'],
        tsconfigRootDir: import.meta.dirname,
      },
    },
    rules: {
      '@typescript-eslint/no-explicit-any': 'error',
    }
  }
);
