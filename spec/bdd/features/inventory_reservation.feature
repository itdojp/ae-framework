Feature: Reserve inventory without going negative or double-booking
  Background:
    Given an item "ITEM-123" with stock 10

  Scenario: Successful reservation
    When I reserve 3 units for order "ORD-1"
    Then the remaining stock should be 7

  Scenario: Prevent negative stock
    When I reserve 11 units for order "ORD-2"
    Then the operation should be rejected with code "INSUFFICIENT_STOCK"

  Scenario: Idempotent by order id
    Given order "ORD-3" already reserved 2 units
    When I reserve 2 units again for order "ORD-3"
    Then the remaining stock should be 8