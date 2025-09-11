name: DDD — Formal Presets + BDD Lint
description: Track aggregate invariants presets and BDD When rules
labels: [ddd, testing, enhancement]
body:
  - type: markdown
    attributes:
      value: |
        Expand aggregate.invariants to formal presets; enforce When rules for Aggregate Root commands. See docs/ddd/bdd-lint.md
  - type: textarea
    id: tasks
    attributes:
      label: Tasks
      description: Presets to add, lint coverage, examples to update
    validations:
      required: false
