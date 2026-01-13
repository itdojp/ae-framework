# Lean Proofs (PoC)

Purpose: Provide a minimal Lean 4 workspace for formal proof experiments.

## Quick start

```bash
cd proofs/lean
lake build
```

## Notes

- This is a PoC workspace; proofs will be added incrementally.
- Planned: CI will run `lake build` and reject unresolved `sorry` markers.
