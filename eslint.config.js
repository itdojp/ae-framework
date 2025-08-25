// eslint v9 flat config (minimal)
import js from '@eslint/js';
import tseslint from 'typescript-eslint';

export default tseslint.config(
  js.configs.recommended,
  ...tseslint.configs.recommended,
  { 
    ignores: ['dist/**', 'artifacts/**', 'node_modules/**', 'apps/**', 'packages/**'] 
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