package inventory

test_deny_negative_quantity {
  deny[_] with input as {"quantity": -1}
}

test_deny_zero_quantity {
  deny[_] with input as {"quantity": 0}
}

test_allow_positive_quantity {
  count(deny) == 0 with input as {"quantity": 1}
}