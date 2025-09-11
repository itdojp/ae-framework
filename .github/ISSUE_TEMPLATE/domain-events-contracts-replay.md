name: DDD — Domain Events → Contracts & Replay
description: Track domain events contracts and replay fixtures
labels: [ddd, testing, enhancement]
body:
  - type: markdown
    attributes:
      value: |
        Generate Zod contracts / replay fixtures from domainEvents[]. See docs/ddd/events.md
  - type: textarea
    id: artifacts
    attributes:
      label: Artifacts
      description: events.json, replay.summary.json, formal/summary.json linkage
    validations:
      required: false
