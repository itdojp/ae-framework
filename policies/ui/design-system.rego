package ui

# Design System Consistency Policy for Phase 6 Quality Gates
# Validates components follow design token standards

# Violation: Components using non-standard colors
violations[v] {
  some c
  input[c].styles.color
  not is_design_token_color(input[c].styles.color)
  v := {
    "id": input[c].id,
    "component": input[c].name,
    "reason": sprintf("using non-standard color: %v", [input[c].styles.color]),
    "severity": "moderate",
    "category": "design-consistency"
  }
}

# Violation: Components using non-standard spacing
violations[v] {
  some c
  input[c].styles.margin
  not is_design_token_spacing(input[c].styles.margin)
  v := {
    "id": input[c].id,
    "component": input[c].name,
    "reason": sprintf("using non-standard margin: %v", [input[c].styles.margin]),
    "severity": "moderate",
    "category": "design-consistency"
  }
}

# Violation: Components using non-standard typography
violations[v] {
  some c
  input[c].styles.font_size
  not is_design_token_font_size(input[c].styles.font_size)
  v := {
    "id": input[c].id,
    "component": input[c].name,
    "reason": sprintf("using non-standard font-size: %v", [input[c].styles.font_size]),
    "severity": "moderate",
    "category": "design-consistency"
  }
}

# Standard design token validation functions
is_design_token_color(color) {
  design_token_colors[_] == color
}

is_design_token_spacing(spacing) {
  design_token_spacing[_] == spacing
}

is_design_token_font_size(size) {
  design_token_font_sizes[_] == size
}

# Design token reference (would be generated from actual design tokens)
design_token_colors := [
  "var(--color-primary-50)",
  "var(--color-primary-500)",
  "var(--color-primary-900)",
  "var(--color-neutral-50)",
  "var(--color-neutral-500)",
  "var(--color-neutral-900)",
  "var(--color-semantic-error)",
  "var(--color-semantic-warning)",
  "var(--color-semantic-success)"
]

design_token_spacing := [
  "var(--spacing-xs)",
  "var(--spacing-sm)",
  "var(--spacing-md)",
  "var(--spacing-lg)",
  "var(--spacing-xl)",
  "0.25rem", "0.5rem", "1rem", "1.5rem", "2rem"
]

design_token_font_sizes := [
  "var(--font-size-xs)",
  "var(--font-size-sm)",
  "var(--font-size-base)",
  "var(--font-size-lg)",
  "var(--font-size-xl)",
  "0.75rem", "0.875rem", "1rem", "1.125rem", "1.25rem"
]