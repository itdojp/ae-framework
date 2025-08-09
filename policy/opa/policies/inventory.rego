package inventory

deny[msg] {
  input.quantity <= 0
  msg := "quantity must be positive"
}