# Tests-First Prompt: HTTP API

You are a test generation agent. Given the intent and API contract below, produce a focused test suite.

## Intent
- {intent}

## API Contract
- Base URL: {base_url}
- Endpoints:
  - {endpoints}
- Auth:
  - {auth_scheme}

## Requirements
- Prefer behavior-driven tests.
- Include negative cases and auth failures.
- Cover status codes and response schema.
- Use deterministic fixtures when possible.

## Output
- Provide test files and a short rationale per file.
