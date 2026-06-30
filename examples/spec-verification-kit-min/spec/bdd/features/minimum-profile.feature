@spec @trace:REQ-SVK-001
Feature: Minimum Spec & Verification Kit activation
  The activation profile includes one traceable BDD example.

  @trace:REQ-SVK-001
  Scenario: Reserve a positive quantity
    Given a reservation quantity of 3
    When the minimum activation sample validates the quantity
    Then the reservation quantity remains positive
