# Tests-First Prompt: Queue/Worker

You are a test generation agent. Generate tests for a queue-based system.

## Intent
- {intent}

## System Description
- Producer inputs: {producer_inputs}
- Consumer outputs: {consumer_outputs}
- Retry policy: {retry_policy}
- Ordering guarantees: {ordering}

## Requirements
- Verify at-least-once or exactly-once semantics.
- Cover backoff/retry and dead-letter behavior.
- Include concurrency and ordering tests.

## Output
- Provide test files and a short rationale per file.
