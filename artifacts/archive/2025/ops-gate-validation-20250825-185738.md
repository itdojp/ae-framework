# ae-framework Operations Gate Validation Report

**Generated**: 2025-08-25 18:46:23 UTC  
**Node**: v20.19.4  
**PM**: pnpm  
**HEAD SHA**: 97004d7ad1c1e546866124def773ed5720fbf5c5  
**Repository**: itdojp/ae-framework  

## Recent Commits
- 97004d7 Policy: bench tolerance/env override, flake opt-in, cassette policy docs (#230)
- c3786ab ci: add Slack alerts for workflow failures (#229)  
- 030aac8 Ops: CI gate hardening (retention, cron, templates, protection helper) (#231)

## Authentication Status
✅ **GitHub CLI**: Authenticated as `ootakazuhiko`  
✅ **Token Scopes**: gist, read:org, repo, workflow  

---

## 1. File & Content Validation

### .github/workflows/pr-verify.yml
**Last Modified**: Aug 25 18:45  
**Status**: ✅ **OK**

**Header (lines 1-10)**:
```yaml
name: PR Verify

on:
  pull_request:
    types: [opened, synchronize, reopened, ready_for_review]

concurrency:
  group: pr-verify-${{ github.ref }}
  cancel-in-progress: true
```

**Key Requirements**:
- ✅ pull_request trigger: Present
- ✅ concurrency setting: Present  
- ✅ retention-days: 14 (line 48)
- ✅ Replay smoke step: Present (line 41) - `AE_RECORDER_MODE=replay`
- ✅ flake-optin job: Present (line 61) with label condition and `continue-on-error: true`

### .github/workflows/nightly-monitoring.yml  
**Last Modified**: Aug 25 18:45  
**Status**: ✅ **OK**

**Header (lines 1-10)**:
```yaml
name: nightly-monitoring

on:
  schedule:
    - cron: "15 19 * * *"   # 毎日 04:15 JST（19:15 UTC）
  workflow_dispatch:

jobs:
  monitor:
    runs-on: ubuntu-latest
```

**Key Requirements**:
- ✅ cron schedule: "15 19 * * *" (line 5) 
- ✅ retention-days: 14 (line 58)

### scripts/ci/compare-bench.mjs
**Last Modified**: Aug 25 18:45  
**Status**: ✅ **OK**

**Header (lines 1-15)**:
```javascript
import { readFile } from 'node:fs/promises';

function relDiff(a, b) { return Math.abs(a - b) / Math.max(a, b); }

async function main() {
  const [f1, f2, tolStr] = process.argv.slice(2);
  
  // tol の決定: env > arg > default
  const tolFromEnv = process.env.BENCH_TOLERANCE ? Number(process.env.BENCH_TOLERANCE) : undefined;
  const tolFromArg = Number(tolStr ?? '');
  const tol = Number.isFinite(tolFromEnv) ? tolFromEnv
            : Number.isFinite(tolFromArg) ? tolFromArg
            : 0.05;
  const tolSource = Number.isFinite(tolFromEnv) ? 'env' : Number.isFinite(tolFromArg) ? 'arg' : 'default';
```

**Key Requirements**:
- ✅ BENCH_TOLERANCE env priority: Present (lines 9-14)
- ✅ tolSource output: Present (lines 14, 29)

### .github/pull_request_template.md
**Last Modified**: Aug 25 17:32  
**Status**: ✅ **OK**

**Content (lines 1-10)**:
```markdown
## Verification Checklist
- [ ] `ae verify` passed locally
- [ ] LLM Replay OK（no cassette diff）
- [ ] Bench delta < 5%（seeded）
- [ ] (optional) `ae qa:flake --times 10` reviewed

## Notes
- Artifacts are uploaded by CI (14 days retention).
- For flaky tests, attach failing seeds if any.
```

**Key Requirements**:
- ✅ Verification Checklist: Present (line 1)
- ✅ 14 days retention mention: Present (line 8)

### README.md  
**Last Modified**: Aug 25 18:45  
**Status**: ✅ **OK**

**Key Sections Found**:
- ✅ CI Gate section: Present (line 319)
- ✅ Benchmark Policy: Present (line 326) 
- ✅ Flake Detection Policy: Present (line 331)
- ✅ Cassette Policy: Present (line 336)

### .gitignore
**Last Modified**: Aug 25 18:45  
**Status**: ✅ **OK**

**Key Requirements**:
- ✅ artifacts/cassettes/: Present (line 56)

---

## 2. Local Reproduction (PR Workflow)

### Dependencies Installation
- ⚠️ **Result**: Warnings present but successful
- **Time**: 5 seconds  
- **Exit Code**: 0
- **Warnings**: 13 deprecated subdependencies, peer dependency issues

### Build Process  
- ❌ **Result**: FAILED
- **Exit Code**: 2
- **Issue**: TypeScript compilation errors
  - Module resolution issues (need .js extensions)
  - Missing dependencies (@anthropic-ai/sdk, @google/generative-ai, openai)
  - Type error in recorder.ts (line 47)

### Verify Command
- ❌ **Result**: FAILED  
- **Exit Code**: 1
- **Issue**: Cannot find module '/home/claudecode/work/ae-framework/dist/cli.js'
- **Artifacts**: No verify.md generated

### Replay Smoke Test
- ❌ **Result**: FAILED
- **Exit Code**: 1  
- **Issue**: Cannot find CLI module
- **Output**: MODULE_NOT_FOUND error

---

## 3. Benchmark Comparison Testing

### Direct Script Test (Environment Override)
- ✅ **Result**: SUCCESS
- **Command**: `BENCH_TOLERANCE=0.03 node scripts/ci/compare-bench.mjs`
- **Exit Code**: 0

**Output Analysis**:
```json
{
  "tol": 0.03,
  "tolSource": "env", 
  "rows": [
    {
      "name": "test1",
      "mean1": 100,
      "mean2": 102, 
      "dMean": 0.0196078431372549,
      "hz1": 10,
      "hz2": 9.8,
      "dHz": 0.019999999999999928,
      "pass": true
    }
  ]
}
```

**Validation**:
- ✅ tolSource: "env" (environment override working)
- ✅ Tolerance respected: 0.03 used instead of default 0.05
- ✅ Pass/fail logic: Working correctly

---

## 4. Flake Test Execution

- ❌ **Result**: FAILED
- **Exit Code**: 1
- **Issue**: Cannot find CLI module  
- **Command**: `node dist/cli.js qa:flake --times 5 --timeoutMs 180000 --workers 50% --pattern "tests/**"`

---

## 5. GitHub CLI State Verification

### Workflow Listings
- ✅ **verify workflows**: Found (pr-verify.yml, active)
- ✅ **nightly workflows**: Found (nightly-monitoring.yml, nightly.yml, active)

### Recent Workflow Runs

**PR Verify (Last 5)**:
- All recent runs: **FAILURE** status
- Most recent: 2025-08-25T09:35:50Z (main branch, HEAD: 97004d7)
- Pattern: Consistent failures across branches

**Nightly Monitoring (Last 5)**:  
- All recent runs: **FAILURE** status
- Most recent: 2025-08-25T09:35:49Z
- Pattern: Consistent failures

### Branch Protection
- ❌ **Status**: NOT CONFIGURED
- **API Response**: "Branch not protected" (404)
- **Issue**: Main branch lacks required status checks

### Repository Secrets
- ⚠️ **SLACK_WEBHOOK_URL**: NOT PRESENT
- **Impact**: Slack notifications will be skipped (expected behavior)
- **Secrets Found**: None

### Manual Workflow Trigger
- ✅ **Nightly Trigger**: Successfully initiated
- **Status**: Workflow dispatch executed

---

## 6. Summary Analysis

### Critical Issues Identified
1. **Build System Failure**: TypeScript compilation prevents CLI generation
2. **Missing Dependencies**: Several npm packages not installed
3. **Branch Protection**: Main branch not protected, no required status checks
4. **CI Failures**: All workflows failing consistently

### Positive Validations  
1. **Configuration Files**: All required files present with correct settings
2. **Bench Script**: Environment override working correctly  
3. **Workflow Structure**: Proper flake opt-in job with continue-on-error
4. **Documentation**: Comprehensive policy sections added
5. **Git Ignore**: Cassette artifacts properly excluded

### Operational Impact
- **Development**: Blocked by build failures
- **CI/CD**: Non-functional due to CLI compilation issues  
- **Quality Gates**: Cannot enforce without working verify command
- **Security**: Branch protection missing

---

## Final Assessment

**Result**: ❌ **REQUIRES IMMEDIATE ATTENTION**

**Priority Fixes Needed**:
1. **HIGH**: Resolve TypeScript compilation errors
2. **HIGH**: Install missing LLM provider dependencies  
3. **MEDIUM**: Configure branch protection with required status checks
4. **MEDIUM**: Investigate CI workflow failures
5. **LOW**: Consider adding SLACK_WEBHOOK_URL secret for notifications

**Next Actions**:
1. Fix module resolution in TypeScript config
2. Add missing dependencies to package.json
3. Fix type errors in recorder.ts
4. Set up branch protection via GitHub API or UI
5. Verify CI functionality after build fixes

---

## Standardized Results Summary

- **Result**: ❌
- **Verify**: exit=1, report=no
- **Replay**: error (MODULE_NOT_FOUND)  
- **Bench**: tol=0.03, tolSource=env, worst dMean=0.020, worst dHz=0.020, pass
- **Flake**: fails=N/A (CLI unavailable), seeds=[]
- **Files**: verify.yml/nightly.yml/compare-bench.mjs/pr-template/README/.gitignore = ok/ok/ok/ok/ok/ok
- **Workflows**: verify/nightly listed=yes/yes
- **Required check**: present=no (branch not protected)
- **Secrets**: SLACK_WEBHOOK_URL present=no