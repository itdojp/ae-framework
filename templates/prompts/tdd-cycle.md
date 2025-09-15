# TDD Cycle Template

> 🌍 Language / 言語: English | 日本語

## Standard TDD Development Prompt

Use this template when implementing features using the ae-framework to ensure proper TDD compliance.

### Phase 1: Intent Definition
```
I need to implement [FEATURE_NAME].

First, let me define the requirements:
1. [REQUIREMENT_1]
2. [REQUIREMENT_2] 
3. [REQUIREMENT_3]

Before proceeding to tests, I will create the formal specifications in specs/ directory.
```

### Phase 2: Formal Specification
```
Now I'll create the formal specifications for [FEATURE_NAME]:

1. Create TLA+ specification in specs/formal/tla+/
2. Define the behavior and invariants
3. Validate the specification

Once specifications are complete, I will proceed to test-first development.
```

### Phase 3: Test-First Development (RED Phase)
```
Following TDD principles, I will now write tests BEFORE any implementation:

1. Create test file: tests/[feature-name].test.ts
2. Write failing tests that describe the expected behavior
3. Run tests to confirm they are RED (failing)
4. Verify test output shows failures

**CRITICAL**: Tests must be RED before proceeding to implementation.

Let me run: npm test
Expected result: Tests should FAIL
```

### Phase 4: Implementation (GREEN Phase)  
```
Now that tests are RED, I'll implement the minimum code to make them pass:

1. Create source file: src/[feature-name].ts
2. Implement only enough code to make tests GREEN
3. Run tests to confirm they pass
4. Verify all tests are now GREEN

Let me run: npm test
Expected result: All tests should PASS
```

### Phase 5: Verification & Validation
```
Now I'll run comprehensive verification:

1. Run full test suite: npm run test:all
2. Check coverage: npm run coverage
3. Run mutation testing if available
4. Validate traceability

All tests must pass and coverage must be >= 80%.
```

### Phase 6: Operations
```
Finally, I'll ensure operational readiness:

1. Update Docker configuration if needed
2. Check CI/CD pipeline compatibility
3. Update documentation
4. Prepare for deployment

The implementation is now complete and follows ae-framework principles.
```

## Guard Checkpoints

Use these checkpoints throughout development:

### Before Writing Code
```bash
ae-framework check --phase 3-tests
# Verify: Tests exist and are RED
```

### After Writing Code  
```bash
ae-framework check --phase 4-code
# Verify: Tests pass and coverage is adequate
```

### Before Commit
```bash
ae-framework guard
# Run all guards to ensure TDD compliance
```

## TDD Violation Prevention

### ❌ Anti-patterns to AVOID:
1. Writing code before tests
2. Skipping test execution 
3. Not confirming RED phase
4. Implementing more than needed for GREEN
5. Committing failing tests

### ✅ Correct TDD Flow:
1. Write test (RED)
2. Run test → confirm failure
3. Write minimal code (GREEN) 
4. Run test → confirm success
5. Refactor if needed
6. Repeat cycle

## Example TDD Session

```
# Phase 1: Requirements
"I need to implement user authentication with password hashing"

# Phase 2: Formal spec  
"Creating TLA+ spec for authentication state machine"

# Phase 3: RED phase
"Writing test for hashPassword function:"
```typescript
test('should hash password with salt', () => {
  const result = hashPassword('password123');
  expect(result).toBeDefined();
  expect(result).not.toBe('password123');
});
```

Running: npm test
❌ EXPECTED: Test fails (function doesn't exist)

# Phase 4: GREEN phase  
"Implementing hashPassword to make test pass:"
```typescript
export function hashPassword(password: string): string {
  // Minimal implementation
  return bcrypt.hashSync(password, 10);
}
```

Running: npm test  
✅ SUCCESS: Test passes

# Phase 5: Verification
Running: npm run test:all
✅ All tests pass
Coverage: 85% (above 80% threshold)

# Complete - Ready for next feature
```

## Integration with ae-framework CLI

The CLI tool supports TDD workflow:

```bash
# Start development session
ae-framework next

# Check current phase compliance  
ae-framework check

# Validate TDD cycle
ae-framework tdd

# Run specific guards
ae-framework guard --name "TDD Guard"
```

This template ensures consistent, compliant TDD development within the ae-framework.
