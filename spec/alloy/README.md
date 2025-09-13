# Alloy 6 Specs (skeleton)

- Place Alloy 6 models here (e.g., `Domain.als`).
- Use LTL/past operators for temporal properties when applicable.

Example skeleton (Domain.als):

```
module Domain

sig State {}

pred Init[s: State] {}

pred Next[s, s': State] {}

assert Safety { all s: State | some s }

check Safety for 5
```

- With Alloy 6, enable temporal extension to check LTL/past.

