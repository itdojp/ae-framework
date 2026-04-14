package ae.policy

import rego.v1

force_condition_to_rule_id := {
  "contains_dependency_manifest_change": "dependency-supply-chain",
  "contains_external_interface_change": "external-interface",
  "contains_context_boundary_change": "context-pack-boundary",
}

policy := as_object(object.get(input, "policy", {}))
pull_request := as_object(object.get(input, "pullRequest", {}))
config := as_object(object.get(input, "config", {}))

policy_labels := as_object(object.get(policy, "labels", {}))
risk_labels := as_object(object.get(policy_labels, "risk", {}))
high_risk_config := as_object(object.get(policy, "highRisk", {}))
classification := as_object(object.get(policy, "classification", {}))
gate_checks := as_object(object.get(policy, "gateChecks", {}))

changed_files := sorted_unique([file |
  some i
  raw := changed_files_raw[i]
  file := string_or_empty(raw)
  file != ""
])

changed_files_raw := as_array(object.get(input, "changedFiles", []))
policy_required_checks := normalize_string_array(object.get(policy, "requiredChecks", []))
high_risk_paths := normalize_string_array(object.get(classification, "highRiskPaths", []))
force_high_risk_conditions := normalize_string_array(object.get(classification, "forceHighRiskWhen", []))
label_requirements := as_array(object.get(policy, "labelRequirements", []))
status_rollup := as_array(object.get(input, "statusRollup", []))
reviews := as_array(object.get(input, "reviews", []))

risk_low := value if {
  value := string_or_empty(object.get(risk_labels, "low", "risk:low"))
  value != ""
} else := "risk:low" if {
  true
}

risk_high := value if {
  value := string_or_empty(object.get(risk_labels, "high", "risk:high"))
  value != ""
} else := "risk:high" if {
  true
}

pull_request_labels := as_array(object.get(pull_request, "labels", []))

current_labels := sorted_unique([label |
  some i
  raw := pull_request_labels[i]
  label := normalize_label(raw)
  label != ""
])

is_risk_label(label) if {
  label == risk_low
}

is_risk_label(label) if {
  label == risk_high
}

current_risk_labels := sorted_unique([label |
  some i
  label := current_labels[i]
  is_risk_label(label)
])

selected_risk_label := current_risk_labels[0] if {
  count(current_risk_labels) == 1
} else := null if {
  true
}

high_risk_path_matches := sorted_unique([file |
  some i
  file := changed_files[i]
  matches_any_pattern(file, high_risk_paths)
])

force_high_risk_triggers := [trigger |
  some i
  condition := force_high_risk_conditions[i]
  rule_id := force_condition_to_rule_id[condition]
  some j
  rule := as_object(label_requirements[j])
  string_or_empty(object.get(rule, "id", "")) == rule_id
  when_any_changed := normalize_string_array(object.get(rule, "whenAnyChanged", []))
  matched_files := sorted_unique([file |
    some k
    file := changed_files[k]
    matches_any_pattern(file, when_any_changed)
  ])
  count(matched_files) > 0
  trigger := {
    "condition": condition,
    "ruleId": rule_id,
    "matchedFiles": matched_files,
  }
]

inferred_risk_level := risk_high if {
  count(high_risk_path_matches) > 0
}

inferred_risk_level := risk_high if {
  count(force_high_risk_triggers) > 0
}

inferred_risk_level := risk_low if {
  count(high_risk_path_matches) == 0
  count(force_high_risk_triggers) == 0
}

inferred_risk := {
  "level": inferred_risk_level,
  "labels": {
    "low": risk_low,
    "high": risk_high,
  },
  "highRiskPathMatches": high_risk_path_matches,
  "forceHighRiskTriggers": force_high_risk_triggers,
}

required_labels := sorted_unique([label |
  some i
  rule := as_object(label_requirements[i])
  when_any_changed := normalize_string_array(object.get(rule, "whenAnyChanged", []))
  some j
  file := changed_files[j]
  matches_any_pattern(file, when_any_changed)
  required := normalize_string_array(object.get(rule, "requireLabels", []))
  some k
  label := required[k]
])

label_present(label) if {
  some i
  current_labels[i] == label
}

missing_required_labels := sorted_unique([label |
  some i
  label := required_labels[i]
  not label_present(label)
])

review_topology_raw := lower(string_or_empty(object.get(config, "reviewTopology", "")))

review_topology := "solo" if {
  review_topology_raw == "solo"
} else := "team" if {
  true
}

review_topology_warning := msg if {
  review_topology_raw != ""
  review_topology_raw != "team"
  review_topology_raw != "solo"
  msg := sprintf("invalid review topology: %s (fallback to team)", [review_topology_raw])
} else := "" if {
  true
}

approval_override_raw := string_or_empty(object.get(config, "approvalOverride", ""))

has_approval_override if {
  approval_override_raw != ""
  regex.match("^-?[0-9]+$", approval_override_raw)
  to_number(approval_override_raw) >= 0
}

approval_override_value := floor(to_number(approval_override_raw)) if {
  has_approval_override
}

approval_override_warning := msg if {
  approval_override_raw != ""
  not regex.match("^-?[0-9]+$", approval_override_raw)
  msg := sprintf(
    "AE_POLICY_MIN_HUMAN_APPROVALS=%s is invalid (expected non-negative integer)",
    [approval_override_raw],
  )
} else := msg if {
  approval_override_raw != ""
  regex.match("^-?[0-9]+$", approval_override_raw)
  to_number(approval_override_raw) < 0
  msg := sprintf(
    "AE_POLICY_MIN_HUMAN_APPROVALS=%s is invalid (expected non-negative integer)",
    [approval_override_raw],
  )
} else := "" if {
  true
}

policy_min_approvals := to_non_negative_int(object.get(high_risk_config, "minHumanApprovals", 1), 1)

topology_min_approvals := 0 if {
  review_topology == "solo"
} else := policy_min_approvals if {
  true
}

effective_min_approvals := approval_override_value if {
  has_approval_override
} else := topology_min_approvals if {
  true
}

min_approvals_source := "override" if {
  has_approval_override
} else := "topology" if {
  review_topology == "solo"
} else := "policy" if {
  true
}

require_policy_labels := object.get(high_risk_config, "requirePolicyLabels", true)
fail_when_required_gate_is_pending := object.get(high_risk_config, "failWhenRequiredGateIsPending", false)

human_reviews := [review |
  some i
  review := as_object(reviews[i])
  is_human_reviewer(review)
]

is_human_reviewer(review) if {
  user := as_object(object.get(review, "user", {}))
  login := lower(string_or_empty(object.get(user, "login", "")))
  login != ""
  user_type := lower(string_or_empty(object.get(user, "type", "")))
  user_type != "bot"
  not endswith(login, "[bot]")
}

review_sort_key(review) := key if {
  submitted_at := string_or_empty(object.get(review, "submittedAt", ""))
  review_id := to_non_negative_int(object.get(review, "id", 0), 0)
  key := sprintf("%s|%020d", [submitted_at, review_id])
}

has_later_human_review(login, review) if {
  some i
  other := human_reviews[i]
  user := as_object(object.get(other, "user", {}))
  lower(string_or_empty(object.get(user, "login", ""))) == login
  review_sort_key(other) > review_sort_key(review)
}

latest_review_state_by_login[login] := state if {
  some i
  review := human_reviews[i]
  user := as_object(object.get(review, "user", {}))
  login := lower(string_or_empty(object.get(user, "login", "")))
  state := upper(string_or_empty(object.get(review, "state", "")))
  not has_later_human_review(login, review)
}

approvals := count({login |
  some login
  latest_review_state_by_login[login] == "APPROVED"
})

check_entries_raw := [entry |
  some i
  item := as_object(status_rollup[i])
  entry := to_check_entry(item)
  entry != null
]

check_entries := [entry |
  some i
  entry := check_entries_raw[i]
  key := check_entry_identity(entry)
  not has_later_check_entry(key, entry, i)
]

to_check_entry(item) := entry if {
  string_or_empty(object.get(item, "__typename", "")) == "CheckRun"
  name := string_or_empty(object.get(item, "name", ""))
  name != ""
  status := upper(string_or_empty(object.get(item, "status", "")))
  status != ""
  conclusion := upper(string_or_empty(object.get(item, "conclusion", "")))
  workflow_name := string_or_empty(object.get(item, "workflowName", ""))
  started_at := string_or_empty(object.get(item, "startedAt", ""))
  completed_at := string_or_empty(object.get(item, "completedAt", ""))
  state := check_run_state(status, conclusion)
  entry := {
    "name": name,
    "state": state,
    "type": "check-run",
    "status": status,
    "conclusion": conclusion,
    "workflowName": workflow_name,
    "startedAt": started_at,
    "completedAt": completed_at,
  }
} else := entry if {
  string_or_empty(object.get(item, "__typename", "")) == "StatusContext"
  context := string_or_empty(object.get(item, "context", ""))
  context != ""
  status := upper(string_or_empty(object.get(item, "state", "")))
  status != ""
  state := status_context_state(status)
  entry := {
    "name": context,
    "state": state,
    "type": "status-context",
    "status": status,
    "conclusion": status,
    "workflowName": "",
    "startedAt": "",
    "completedAt": "",
  }
} else := null if {
  true
}

check_entry_identity(entry) := sprintf("%s::%s", [
  string_or_empty(object.get(entry, "type", "")),
  string_or_empty(object.get(entry, "name", "")),
])

check_entry_timestamp(entry) := completed_at if {
  completed_at := string_or_empty(object.get(entry, "completedAt", ""))
  completed_at != ""
} else := started_at if {
  started_at := string_or_empty(object.get(entry, "startedAt", ""))
  started_at != ""
} else := "" if {
  true
}

check_entry_sort_key(entry, index) := sprintf("%s|%020d", [
  check_entry_timestamp(entry),
  index,
])

has_later_check_entry(key, entry, index) if {
  some j
  other := check_entries_raw[j]
  j != index
  check_entry_identity(other) == key
  check_entry_sort_key(other, j) > check_entry_sort_key(entry, index)
}

check_run_state(status, conclusion) := "pending" if {
  status != "COMPLETED"
} else := "success" if {
  conclusion == "SUCCESS"
} else := "success" if {
  conclusion == "SKIPPED"
} else := "success" if {
  conclusion == "NEUTRAL"
} else := "pending" if {
  conclusion == ""
} else := "failure" if {
  true
}

status_context_state(status) := "success" if {
  status == "SUCCESS"
} else := "pending" if {
  status == "PENDING"
} else := "failure" if {
  status == "FAILURE"
} else := "failure" if {
  status == "ERROR"
} else := "neutral" if {
  true
}

matches_any_pattern(value, patterns) if {
  some i
  pattern := patterns[i]
  pattern != ""
  glob.match(pattern, ["/"], value)
}

is_glob_pattern(pattern) if {
  contains(pattern, "*")
}

is_glob_pattern(pattern) if {
  contains(pattern, "?")
}

is_glob_pattern(pattern) if {
  contains(pattern, "[")
}

is_glob_pattern(pattern) if {
  contains(pattern, "]")
}

is_glob_pattern(pattern) if {
  contains(pattern, "{")
}

is_glob_pattern(pattern) if {
  contains(pattern, "}")
}

is_glob_pattern(pattern) if {
  contains(pattern, "(")
}

is_glob_pattern(pattern) if {
  contains(pattern, ")")
}

is_glob_pattern(pattern) if {
  contains(pattern, "!")
}

is_glob_pattern(pattern) if {
  contains(pattern, "+")
}

is_glob_pattern(pattern) if {
  contains(pattern, "@")
}

matches_check_pattern(name, pattern) if {
  is_glob_pattern(pattern)
  glob.match(pattern, ["/"], name)
}

matches_check_pattern(name, pattern) if {
  not is_glob_pattern(pattern)
  name == pattern
}

evaluate_check_requirement(entries, patterns) := {
  "status": "missing",
  "matches": [],
  "reason": "no-check-pattern",
} if {
  normalized := sorted_unique(normalize_string_array(patterns))
  count(normalized) == 0
} else := {
  "status": "missing",
  "matches": [],
  "reason": "not-found",
} if {
  normalized := sorted_unique(normalize_string_array(patterns))
  count(normalized) > 0
  matches := [entry |
    some i
    entry := entries[i]
    some j
    pattern := normalized[j]
    matches_check_pattern(string_or_empty(object.get(entry, "name", "")), pattern)
  ]
  count(matches) == 0
} else := {
  "status": "failure",
  "matches": matches,
  "reason": "failed",
} if {
  normalized := sorted_unique(normalize_string_array(patterns))
  matches := [entry |
    some i
    entry := entries[i]
    some j
    pattern := normalized[j]
    matches_check_pattern(string_or_empty(object.get(entry, "name", "")), pattern)
  ]
  count(matches) > 0
  some i
  string_or_empty(object.get(matches[i], "state", "")) == "failure"
} else := {
  "status": "pending",
  "matches": matches,
  "reason": "pending",
} if {
  normalized := sorted_unique(normalize_string_array(patterns))
  matches := [entry |
    some i
    entry := entries[i]
    some j
    pattern := normalized[j]
    matches_check_pattern(string_or_empty(object.get(entry, "name", "")), pattern)
  ]
  count(matches) > 0
  not matches_has_state(matches, "failure")
  matches_has_state(matches, "pending")
} else := {
  "status": "success",
  "matches": matches,
  "reason": "success",
} if {
  normalized := sorted_unique(normalize_string_array(patterns))
  matches := [entry |
    some i
    entry := entries[i]
    some j
    pattern := normalized[j]
    matches_check_pattern(string_or_empty(object.get(entry, "name", "")), pattern)
  ]
  count(matches) > 0
  not matches_has_state(matches, "failure")
  not matches_has_state(matches, "pending")
}

matches_has_state(matches, expected_state) if {
  some i
  string_or_empty(object.get(matches[i], "state", "")) == expected_state
}

required_checks := [check_name |
  some i
  check_name := policy_required_checks[i]
  check_name != "policy-gate"
]

required_check_results := [entry |
  some i
  check_name := required_checks[i]
  entry := {
    "checkName": check_name,
    "result": evaluate_check_requirement(check_entries, [check_name]),
  }
]

gate_patterns_for_label(label) := normalize_string_array(object.get(as_object(object.get(gate_checks, label, {})), "patterns", []))

is_high_risk if {
  selected_risk_label == risk_high
}

is_high_risk if {
  inferred_risk_level == risk_high
}

default gate_check_results := []

gate_check_results := [entry |
  is_high_risk
  some i
  label := required_labels[i]
  label_present(label)
  patterns := gate_patterns_for_label(label)
  entry := {
    "label": label,
    "patterns": patterns,
    "result": evaluate_check_requirement(check_entries, patterns),
  }
]

error_messages contains msg if {
  count(current_risk_labels) == 0
  msg := sprintf("missing risk label: %s or %s", [risk_low, risk_high])
}

error_messages contains msg if {
  count(current_risk_labels) > 1
  msg := sprintf("multiple risk labels: %s", [concat(", ", current_risk_labels)])
}

error_messages contains msg if {
  selected_risk_label != null
  selected_risk_label != inferred_risk_level
  msg := sprintf("risk label mismatch: expected %s, found %s", [inferred_risk_level, selected_risk_label])
}

error_messages contains msg if {
  some i
  item := required_check_results[i]
  string_or_empty(object.get(item.result, "status", "")) == "failure"
  msg := sprintf("required check failed: %s", [item.checkName])
}

error_messages contains msg if {
  is_high_risk
  approvals < effective_min_approvals
  msg := sprintf("human approvals are insufficient: required %d, got %d", [effective_min_approvals, approvals])
}

error_messages contains msg if {
  is_high_risk
  require_policy_labels
  count(missing_required_labels) > 0
  msg := sprintf("missing required labels: %s", [concat(", ", missing_required_labels)])
}

error_messages contains msg if {
  is_high_risk
  some i
  item := gate_check_results[i]
  status := string_or_empty(object.get(item.result, "status", ""))
  status == "failure"
  msg := sprintf("required gate check not green for label %s (%s)", [item.label, status])
}

error_messages contains msg if {
  is_high_risk
  some i
  item := gate_check_results[i]
  status := string_or_empty(object.get(item.result, "status", ""))
  status == "missing"
  msg := sprintf("required gate check not green for label %s (%s)", [item.label, status])
}

error_messages contains msg if {
  is_high_risk
  fail_when_required_gate_is_pending
  some i
  item := gate_check_results[i]
  string_or_empty(object.get(item.result, "status", "")) == "pending"
  msg := sprintf("required gate check pending for label %s", [item.label])
}

warnings_messages contains msg if {
  review_topology_warning != ""
  msg := review_topology_warning
}

warnings_messages contains msg if {
  approval_override_warning != ""
  msg := approval_override_warning
}

warnings_messages contains msg if {
  some i
  item := required_check_results[i]
  string_or_empty(object.get(item.result, "status", "")) == "pending"
  msg := sprintf("required check not ready yet: %s (%s)", [item.checkName, "pending"])
}

warnings_messages contains msg if {
  some i
  item := required_check_results[i]
  string_or_empty(object.get(item.result, "status", "")) == "missing"
  msg := sprintf("required check not ready yet: %s (%s)", [item.checkName, "missing"])
}

warnings_messages contains msg if {
  is_high_risk
  not require_policy_labels
  count(missing_required_labels) > 0
  msg := sprintf("policy labels missing (allowed by config): %s", [concat(", ", missing_required_labels)])
}

warnings_messages contains msg if {
  is_high_risk
  not fail_when_required_gate_is_pending
  some i
  item := gate_check_results[i]
  string_or_empty(object.get(item.result, "status", "")) == "pending"
  msg := sprintf("required gate check pending for label %s", [item.label])
}

warnings_messages contains msg if {
  is_high_risk
  some i
  label := required_labels[i]
  label_present(label)
  count(gate_patterns_for_label(label)) == 0
  msg := sprintf("no gate_checks mapping configured for label %s", [label])
}

pr_body := string_or_empty(object.get(pull_request, "body", ""))

has_section(section_name) if {
  body := lower(pr_body)
  section := lower(section_name)
  contains(body, section)
}

warnings_messages contains msg if {
  not has_section("Rollback")
  msg := "PR body is missing Rollback section"
}

warnings_messages contains msg if {
  not has_section("Acceptance")
  not has_section("受入基準")
  msg := "PR body is missing Acceptance section"
}

errors := sort(error_messages)
warnings := sort(warnings_messages)

decision := {
  "ok": count(errors) == 0,
  "errors": errors,
  "warnings": warnings,
  "inferredRisk": inferred_risk,
  "selectedRiskLabel": selected_risk_label,
  "currentRiskLabels": current_risk_labels,
  "reviewTopology": review_topology,
  "approvals": approvals,
  "minApprovals": effective_min_approvals,
  "policyMinApprovals": policy_min_approvals,
  "topologyMinApprovals": topology_min_approvals,
  "effectiveMinApprovals": effective_min_approvals,
  "minApprovalsSource": min_approvals_source,
  "requiredLabels": required_labels,
  "missingRequiredLabels": missing_required_labels,
  "requiredCheckResults": required_check_results,
  "gateCheckResults": gate_check_results,
}

normalize_label(value) := out if {
  is_string(value)
  out := trim_space(value)
} else := out if {
  is_object(value)
  out := string_or_empty(object.get(value, "name", ""))
} else := "" if {
  true
}

string_or_empty(value) := out if {
  is_string(value)
  out := trim_space(value)
} else := "" if {
  true
}

normalize_string_array(values) := [item |
  some i
  raw := as_array(values)[i]
  item := string_or_empty(raw)
  item != ""
]

sorted_unique(values) := sort({item |
  some i
  item := values[i]
})

as_array(value) := value if {
  is_array(value)
} else := [] if {
  true
}

as_object(value) := value if {
  is_object(value)
} else := {} if {
  true
}

to_non_negative_int(value, fallback) := out if {
  num := to_number(value)
  num >= 0
  out := floor(num)
} else := fallback if {
  true
}
