# Domain (Z notation, Phase 0)

This is a **minimal** Z spec aligned with `spec/tla/DomainSpec.tla` and (partially) with `spec/alloy/Domain.als`.

Note:
- The `onHand <= MaxOnHand` bound is aligned with the TLA+ skeleton.
- The current Alloy skeleton does **not** model `MaxOnHand` yet (Phase 0).

> Note: The content is written in LaTeX-ish Z using ASCII-only tokens so it can be reviewed in plain text.

## Z (LaTeX-ish)

```text
% ---- Parameters ----
\begin{axdef}
  MaxQty, MaxOnHand: \nat
\where
  MaxQty > 0 \land MaxOnHand > 0
\end{axdef}

% ---- State ----
\begin{schema}{DomainState}
  onHand, allocated: \nat
\where
  allocated \leq onHand \land onHand \leq MaxOnHand
\end{schema}

% ---- Init ----
\begin{schema}{InitDomainState}
  DomainState
\where
  onHand = 0 \land allocated = 0
\end{schema}

% ---- Operations ----

% Receive: increase onHand by qty?
\begin{schema}{Receive}
  \Delta DomainState
  qty?: \nat
\where
  qty? \in 1 .. MaxQty \land onHand + qty? \leq MaxOnHand \land
  onHand' = onHand + qty? \land allocated' = allocated
\end{schema}

% Allocate: increase allocated by qty?
\begin{schema}{Allocate}
  \Delta DomainState
  qty?: \nat
\where
  qty? \in 1 .. MaxQty \land allocated + qty? \leq onHand \land
  allocated' = allocated + qty? \land onHand' = onHand
\end{schema}

% Ship: decrease both onHand and allocated by qty?
\begin{schema}{Ship}
  \Delta DomainState
  qty?: \nat
\where
  qty? \in 1 .. MaxQty \land qty? \leq allocated \land
  allocated' = allocated - qty? \land onHand' = onHand - qty?
\end{schema}
```

## Cross-reference

- TLA+ invariant: `state.onHand >= 0 /\ state.allocated <= state.onHand /\ state.onHand <= MaxOnHand`
  - Z: `DomainState` constraints.
- Alloy invariant: `s.onHand >= 0 and s.allocated <= s.onHand`
  - Z: subset of `DomainState` constraints: `allocated <= onHand` (Alloy omits `onHand <= MaxOnHand`).
