# Security three-gate review summary

- Generated at: 2026-05-07T00:00:00.000Z
- Total reviews: 2
- Needs human review: 1
- Confirmed: 0
- Rejected: 0
- Waived: 0
- Out of scope: 1
- Dead-code root causes: 0
- Trust-boundary root causes: 0
- Out-of-scope root causes: 1
- Warnings: 0

## Reviews

| Finding | Severity | Result | Dead Code | Trust Boundary | Scope | Root cause |
| --- | --- | --- | --- | --- | --- | --- |
| SEC-FINDING-001 | high | needs-human-review | pass | pass | pass | n/a |
| SEC-FINDING-002 | low | out-of-scope | unknown | unknown | fail | out-of-scope |

## Review detail

### SEC-FINDING-001

- Severity: high
- Result: needs-human-review
- False-positive root cause: n/a
- Dead Code: pass — At least one affected location overlaps the security-code-map candidate locations for the same claim.
- Trust Boundary: pass — Matched attacker-controlled trust boundary: TB-CACHE.
- Scope: pass — All affected paths are covered by audit scope inScope globs (src/**/*.ts).
- Reviewer notes:
  - Severity preserved from finding: high.
  - Rule-based MVP review only; exploitability confirmation and full reachability analysis are out of scope.
  - Candidate finding remains unresolved and requires human security review before confirmation.

### SEC-FINDING-002

- Severity: low
- Result: out-of-scope
- False-positive root cause: out-of-scope
- Dead Code: unknown — Dead-code reachability was not evaluated because the scope gate failed first.
- Trust Boundary: unknown — Trust-boundary involvement was not evaluated because the scope gate failed first.
- Scope: fail — At least one affected path is excluded by audit scope outOfScope globs: tests/**.
- Reviewer notes:
  - Severity preserved from finding: low.
  - Rule-based MVP review only; exploitability confirmation and full reachability analysis are out of scope.
  - Trust boundary involvement is unknown from available scope/code-map evidence.
  - Classified as out-of-scope based on audit scope glob rules.
