# Quick Hermetic Test Validation Report

**Generated:** 2025-08-20T00:42:12.153Z
**Overall Score:** 🟠 47/100
**Hermetic Level:** POOR

## 📊 Hermetic Properties Summary

| Property | Score | Status | Issues |
|----------|-------|--------|--------|
| Dependencies | 0/100 | 🔴 | 47 |
| FileSystem | 78/100 | 🟢 | 23 |
| Network | 100/100 | 🌟 | 1 |
| Timing | 9/100 | 🔴 | 34 |
| TestStructure | 94/100 | 🌟 | 0 |

## 🚨 Critical Hermetic Violations

- **filesystem** in `tests/commands/slash-command-manager.test.ts`:13
  Test contains file system operations - should be isolated
  `await fs.promises.mkdir(testDir, { recursive: true });`

- **filesystem** in `tests/commands/slash-command-manager.test.ts`:19
  Test contains file system operations - should be isolated
  `await fs.promises.rm(testDir, { recursive: true, force: true });`

- **filesystem** in `tests/commands/slash-command-manager.test.ts`:190
  Test contains file system operations - should be isolated
  `await fs.promises.mkdir(steeringDir, { recursive: true });`

- **filesystem** in `tests/commands/slash-command-manager.test.ts`:191
  Test contains file system operations - should be isolated
  `await fs.promises.writeFile(`

- **filesystem** in `tests/container/container-agent.test.ts`:17
  Test contains file system operations - should be isolated
  `tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'container-agent-test-'));`

- **filesystem** in `tests/container/container-agent.test.ts`:28
  Test contains file system operations - should be isolated
  `await fs.rm(tempDir, { recursive: true });`

- **environment** in `tests/container/container-agent.test.ts`:42
  Test depends on environment variables - should be controlled
  `if (process.env.CI && result.data?.degradedMode) {`

- **filesystem** in `tests/container/container-agent.test.ts`:51
  Test contains file system operations - should be isolated
  `const files = await fs.readdir(tempDir);`

- **environment** in `tests/container/container-agent.test.ts`:75
  Test depends on environment variables - should be controlled
  `} else if (process.env.CI) {`

- **environment** in `tests/container/container-agent.test.ts`:164
  Test depends on environment variables - should be controlled
  `if (process.env.CI && !result.success) {`

... and 71 more issues

## 📋 Recommendations

🚨 **Critical hermetic violations detected!**

1. Implement proper test isolation immediately
2. Mock all external dependencies
3. Use fake timers for time-dependent tests
4. Avoid file system operations in tests

