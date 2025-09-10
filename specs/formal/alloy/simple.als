open util/integer

sig Item { stock: Int }

fact NonNegativeStock {
  all i: Item | i.stock >= 0
}

assert Trivial {
  all i: Item | i.stock >= 0
}

check Trivial for 3 but 3 Int

