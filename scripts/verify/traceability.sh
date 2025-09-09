#!/usr/bin/env bash
set -euo pipefail
# Delegates to Node builder for richer traceability (CSV + JSON)
node scripts/verify/build-traceability.mjs
