---
name: Windows Installation Issue
about: Report issues related to Windows installation and build process
title: '[Windows] TypeScript build failures and setup script compatibility issues'
labels: bug, windows, typescript, build
assignees: ''
---

## 🐛 Problem Summary

Windows users are experiencing multiple TypeScript compilation errors and script compatibility issues during initial installation and setup.

## 🔍 Issue Details

### Primary Issues Identified:

1. **TypeScript rootDir Configuration Error**
   - `packages/spec-compiler/src/*` files are not under the expected `rootDir` (`./src`)
   - Affects: `compiler.ts`, `types.ts`, `strict-schema.ts`, `index.ts`

2. **TypeScript Strict Null Checks Violations**
   - Over 600+ `TS2532` and `TS2345` errors due to undefined object access
   - Major affected files include agents, services, utils modules

3. **Windows Command Compatibility**
   - `setup-hooks` script uses Unix `cp` and `chmod` commands
   - Not compatible with Windows Command Prompt/PowerShell

## 📋 Error Log Analysis

**Total Errors:** 600+ TypeScript compilation errors

**Error Categories:**
- `TS6059`: rootDir path violations (4 occurrences)
- `TS2532`: Object possibly undefined (500+ occurrences) 
- `TS2345`: Type assignment errors (100+ occurrences)
- `TS2538`: Index type errors (50+ occurrences)

**Most Affected Files:**
- `src/agents/*` (200+ errors)
- `src/services/*` (150+ errors) 
- `src/utils/*` (100+ errors)
- `packages/spec-compiler/src/*` (50+ errors)

## 🖥️ Environment

- **OS**: Windows 11
- **Node.js**: 18+ (assumed)
- **Package Manager**: pnpm
- **TypeScript**: 5.9.2
- **Installation Method**: `git clone` + `pnpm install` + `pnpm run build`

## 🔄 Reproduction Steps

1. Clone repository on Windows system
2. Run `pnpm install` (succeeds)
3. Run `npx playwright install` (succeeds)
4. Run `pnpm run build` (fails with 600+ TypeScript errors)
5. Run `pnpm run setup-hooks` (fails with Windows compatibility issue)

## ✅ Proposed Solutions

### 1. Fix TypeScript Configuration

**Option A: Update tsconfig.json**
```json
{
  "compilerOptions": {
    "rootDir": ".",
    // ... other options
  },
  "include": ["src/**/*", "packages/**/*"]
}
```

**Option B: Create separate tsconfig for packages**
```json
// packages/spec-compiler/tsconfig.json
{
  "extends": "../../tsconfig.json",
  "compilerOptions": {
    "rootDir": "./src",
    "outDir": "./dist"
  },
  "include": ["src/**/*"]
}
```

### 2. Fix Null Safety Issues

Enable gradual migration approach:
```json
{
  "compilerOptions": {
    "noUncheckedIndexedAccess": false, // Temporarily disable
    "strict": false, // Consider gradual migration
  }
}
```

### 3. Windows Script Compatibility

**Update package.json:**
```json
{
  "scripts": {
    "setup-hooks": "node scripts/setup-hooks.js",
    "setup-hooks:unix": "cp scripts/hooks/pre-commit .git/hooks/pre-commit && chmod +x .git/hooks/pre-commit"
  }
}
```

**Create cross-platform setup script:**
```javascript
// scripts/setup-hooks.js
const fs = require('fs');
const path = require('path');
const os = require('os');

const isWindows = os.platform() === 'win32';
// Windows-compatible hook setup implementation
```

## 💡 Immediate Workarounds

For Windows users encountering this issue:

1. **Skip build for now:**
   ```bash
   # Install dependencies only
   pnpm install
   npx playwright install
   
   # Skip build step temporarily
   # pnpm run build
   ```

2. **Manual hook setup (Git Bash/WSL):**
   ```bash
   # Use Git Bash or WSL for hook setup
   cp scripts/hooks/pre-commit .git/hooks/pre-commit
   chmod +x .git/hooks/pre-commit
   ```

## 🎯 Priority

**High Priority** - This affects all Windows users attempting fresh installation.

## 📊 Impact Assessment

- **User Experience**: Major - Windows users cannot complete setup
- **Development**: Medium - Affects new contributor onboarding  
- **CI/CD**: Low - Primarily affects local development

## 🔗 Related Issues

- TypeScript configuration needs review
- Cross-platform compatibility requires attention
- Monorepo structure may need tsconfig adjustments

## 📝 Additional Context

This issue was identified during a fresh Windows installation attempt. The high number of TypeScript errors suggests this may be related to recent changes in strict type checking configuration or monorepo structure modifications.

Log file analysis shows the installation process succeeds through dependency installation but fails at the TypeScript compilation step, preventing users from completing the setup process.