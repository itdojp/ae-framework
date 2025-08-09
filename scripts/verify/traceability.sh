#!/usr/bin/env bash
set -euo pipefail
# BDD feature のシナリオ名とテスト/実装の参照を集計（簡易）
FEATURES=$(grep -R "^\s*Scenario:" -n specs/bdd/features | sed 's/:\s*Scenario:/#/')
echo "Scenario,Test,Implementation" > traceability.csv
while IFS= read -r line; do
  file=$(echo "$line" | cut -d: -f1)
  scenario=$(echo "$line" | cut -d# -f2-)
  test_ref=$(grep -R "${scenario}" -n tests || true | cut -d: -f1 | head -n1)
  impl_ref=$(grep -R "${scenario}" -n src || true | cut -d: -f1 | head -n1)
  echo "${scenario},${test_ref:-N/A},${impl_ref:-N/A}" >> traceability.csv
done <<< "$FEATURES"
echo "Generated traceability.csv"