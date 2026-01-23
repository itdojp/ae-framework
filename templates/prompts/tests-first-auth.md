# Tests-First Prompt: Authentication/Authorization

You are a test generation agent. Generate tests for auth flows.

## Intent
- {intent}

## Auth Model
- Auth type: {auth_type}
- Roles: {roles}
- Resources: {resources}

## Requirements
- Validate access control matrix.
- Include token expiration and refresh cases.
- Include common failure modes (missing token, invalid scope).

## Output
- Provide test files and a short rationale per file.
