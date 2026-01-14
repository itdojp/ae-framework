namespace AEFrameworkProofs

/-- A minimal gate predicate: pass when score meets or exceeds threshold. -/
def passesGate (score threshold : Nat) : Prop := threshold <= score

/-- If a gate passes at a higher threshold, it also passes at any lower threshold. -/
theorem passesGate_monotone {score t1 t2 : Nat} (hPass : passesGate score t1)
    (hLower : t2 <= t1) : passesGate score t2 := by
  exact Nat.le_trans hLower hPass

end AEFrameworkProofs
