package ui

# UI Accessibility Policy Rules for Phase 6 Quality Gates
# Validates components against WCAG 2.1 AA requirements

# Violation: Presentational elements without proper labeling
violations[v] {
  some c
  input[c].role == "presentation"
  not input[c].aria_label
  v := {
    "id": input[c].id,
    "component": input[c].name,
    "reason": "presentational element missing aria-label",
    "severity": "critical",
    "wcag": "4.1.2"
  }
}

# Violation: Interactive elements without accessible names
violations[v] {
  some c
  input[c].interactive == true
  not input[c].aria_label
  not input[c].aria_labelledby
  not input[c].title
  not has_text_content(input[c])
  v := {
    "id": input[c].id,
    "component": input[c].name,
    "reason": "interactive element lacks accessible name",
    "severity": "critical",
    "wcag": "4.1.2"
  }
}

# Violation: Form inputs without labels
violations[v] {
  some c
  input[c].type == "input"
  not input[c].aria_label
  not input[c].aria_labelledby
  not has_associated_label(input[c])
  v := {
    "id": input[c].id,
    "component": input[c].name,
    "reason": "form input missing label association",
    "severity": "critical",
    "wcag": "3.3.2"
  }
}

# Violation: Poor color contrast
violations[v] {
  some c
  input[c].contrast_ratio < 4.5
  input[c].font_size < 18
  v := {
    "id": input[c].id,
    "component": input[c].name,
    "reason": sprintf("color contrast ratio %v below 4.5:1 threshold", [input[c].contrast_ratio]),
    "severity": "serious",
    "wcag": "1.4.3"
  }
}

# Helper functions
has_text_content(element) {
  element.text_content
  trim_space(element.text_content) != ""
}

has_associated_label(element) {
  element.label_for == element.id
}