# @ae-framework/spec-compiler

> AE-Spec to AE-IR compiler for single source of truth (SSOT)

## Overview

The `@ae-framework/spec-compiler` package provides a compiler that transforms natural language AE-Spec markdown files into structured AE-IR (AI-Enhanced Intermediate Representation) JSON format. This establishes a single source of truth for all specifications in the ae-framework.

## Features

- 📝 **Markdown to JSON**: Convert AE-Spec markdown to structured AE-IR
- 🔍 **Quality Linting**: Comprehensive validation and quality checks
- 🏗️ **SSOT Integration**: Single source of truth for all framework phases
- 🛠️ **CLI Tools**: Command-line interface for compilation and validation
- 🧪 **Type Safety**: Full TypeScript support with comprehensive types

## Installation

```bash
# Install as dependency
npm install @ae-framework/spec-compiler

# Install CLI globally (optional)
npm install -g @ae-framework/spec-compiler
```

## API Usage

### Basic Compilation

```typescript
import { AESpecCompiler } from '@ae-framework/spec-compiler';

const compiler = new AESpecCompiler();

// Compile markdown to AE-IR
const ir = await compiler.compile({
  inputPath: 'spec/my-spec.md',
  outputPath: '.ae/ae-ir.json',
  validate: true
});

console.log('Entities:', ir.domain.map(e => e.name));
```

### Linting and Validation

```typescript
import { AESpecCompiler } from '@ae-framework/spec-compiler';

const compiler = new AESpecCompiler();
const ir = await compiler.compile({ inputPath: 'spec/my-spec.md' });

// Lint for quality issues
const lintResult = await compiler.lint(ir);

if (!lintResult.passed) {
  console.log('Issues found:');
  lintResult.issues.forEach(issue => {
    console.log(`${issue.severity}: ${issue.message}`);
  });
}
```

## CLI Usage

### Compile Command

```bash
# Compile markdown to JSON
ae-spec compile -i spec/my-spec.md -o .ae/ae-ir.json

# Compile with validation disabled
ae-spec compile -i spec/my-spec.md --no-validate

# Output to stdout
ae-spec compile -i spec/my-spec.md
```

### Lint Command

```bash
# Lint AE-IR file
ae-spec lint -i .ae/ae-ir.json

# Lint with custom thresholds
ae-spec lint -i .ae/ae-ir.json --max-errors 0 --max-warnings 5
```

### Validate Command

```bash
# Full validation (compile + lint)
ae-spec validate -i spec/my-spec.md

# Custom thresholds
ae-spec validate -i spec/my-spec.md --max-errors 0 --max-warnings 10
```

## AE-Spec Markdown Format

### Basic Structure

```markdown
# My Application Specification

Brief description of the application.

## Glossary

- **User**: A person who interacts with the system
- **Product**: An item available for purchase

## Domain

### User
- **id** (UUID, required) - Unique identifier
- **email** (string, required) - User email address
- **name** (string) - Display name

### Product
- **id** (UUID, required) - Unique identifier
- **name** (string, required) - Product name
- **price** (decimal, required) - Product price

## Invariants

- User email must be unique
- Product price must be greater than zero
- Stock quantity cannot be negative

## Use Cases

### Create User
- User provides email and name
- System validates email uniqueness
- System creates user account
- System sends confirmation email

### Purchase Product
- User selects product
- System checks product availability
- System processes payment
- System updates inventory

## API

- POST /users - Create new user
- GET /users/{id} - Get user details
- POST /products - Create product
- GET /products - List products
- POST /orders - Create order
```

## AE-IR JSON Format

The compiler generates structured JSON following the AEIR interface:

```json
{
  "version": "1.0.0",
  "metadata": {
    "name": "My Application Specification",
    "created": "2025-01-20T10:00:00Z",
    "updated": "2025-01-20T10:00:00Z"
  },
  "domain": [
    {
      "name": "User",
      "fields": [
        {
          "name": "id",
          "type": "UUID",
          "required": true
        },
        {
          "name": "email",
          "type": "string",
          "required": true
        }
      ]
    }
  ],
  "invariants": [
    {
      "id": "INV_001",
      "description": "User email must be unique",
      "expression": "User.email.unique",
      "entities": ["User"],
      "severity": "error"
    }
  ],
  "api": [
    {
      "method": "POST",
      "path": "/users",
      "summary": "Create new user"
    }
  ]
}
```

## Integration with ae-framework

The spec-compiler integrates seamlessly with ae-framework phases:

```typescript
// Phase integration example
import { HybridTDDSystem } from 'ae-framework';
import { AESpecCompiler } from '@ae-framework/spec-compiler';

const system = new HybridTDDSystem();
const compiler = new AESpecCompiler();

// Compile spec to AE-IR
const ir = await compiler.compile({
  inputPath: 'spec/ae-spec.md',
  validate: true
});

// Use AE-IR as single source of truth for all phases
await system.processRequest({
  phase: PhaseType.USER_STORIES,
  input: { aeIR: ir },
  context: executionContext
});
```

## Quality Rules

The linter enforces these quality rules:

### Structure Rules
- `STRUCT_001`: Specification must have a name
- `STRUCT_002`: At least one domain entity should be defined
- `STRUCT_003`: API endpoints should be documented

### Business Logic Rules  
- `BIZ_001`: Entities should have associated business rules

### Consistency Rules
- `CONS_001`: Entity relationships must reference existing entities

### Completeness Rules
- `COMP_001`: Entities should have at least one required field

## Contributing

1. Add new parsing logic in `src/compiler.ts`
2. Update types in `src/types.ts`
3. Add corresponding CLI commands in `src/cli.ts`
4. Write tests for new functionality
5. Update this README

## License

MIT License - see LICENSE file for details.