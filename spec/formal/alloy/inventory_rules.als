open util/integer

sig Sku {}
sig Stock { qty: Int }

fact NonNegative {
  all s: Stock | s.qty >= 0
}

pred ReserveOk[s: Stock, q: Int] {
  q > 0 and q <= s.qty
}

assert ReserveNeverNegative {
  all s: Stock, q: Int | ReserveOk[s, q] implies (s.qty - q) >= 0
}

check ReserveNeverNegative for 3 but 5 Int

