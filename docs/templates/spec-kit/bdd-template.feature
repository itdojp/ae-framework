# Template: copy to specs/bdd/features/<feature>.feature
# Tags: @spec @trace:<trace-id>

Feature: <feature title>
  As a <role>
  I want <goal>
  So that <benefit>

  Background:
    Given <initial state>

  @spec @trace:<trace-id>
  Scenario: <scenario title>
    Given <precondition>
    When <action>
    Then <expected outcome>
    And <secondary outcome>
