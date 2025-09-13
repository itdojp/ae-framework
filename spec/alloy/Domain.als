module Domain

// Minimal Alloy skeleton for illustration. Replace with domain model.

sig State {
  onHand: Int,
  allocated: Int
}

pred Init[s: State] { s.onHand = 0 and s.allocated = 0 }

pred Invariant[s: State] { s.onHand >= 0 and s.allocated <= s.onHand }

assert Safety { all s: State | Invariant[s] }

check Safety for 5 Int, 3 State
