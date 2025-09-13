# TLA+ Specs (skeleton)

- Place TLA+ modules here (e.g., `DomainSpec.tla`).
- Start with safety invariants; add liveness as needed.
- Keep models small and composable; prefer assumptions per module.

Example skeleton (DomainSpec.tla):

```
------------------------------ MODULE DomainSpec ------------------------------
EXTENDS Naturals, Sequences

(* --algorithm sketch
variables state \in {"Init"}, history = <<>>;
end algorithm; *)

Init == TRUE
Next == UNCHANGED << >>

Invariant == TRUE

=============================================================================
```

- To verify with TLC: `tlc2 DomainSpec.tla` (if installed)
- To verify with Apalache: `apalache-mc check --inv=Invariant DomainSpec.tla`

