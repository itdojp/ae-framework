#!/usr/bin/env bash
set -euo pipefail

echo "Running all CI checks locally..."

# Lint specifications
echo "=== Spec Lint ==="
make spec:lint || echo "Spec lint failed"

# Formal verification
echo "=== Formal Check ==="
make formal:check || echo "Formal check failed"

# Run all tests
echo "=== Acceptance Tests ==="
make test:acceptance || echo "Acceptance tests failed"

echo "=== Property Tests ==="
make test:property || echo "Property tests failed"

echo "=== Model-Based Tests ==="
make test:mbt || echo "MBT failed"

echo "=== Mutation Tests ==="
make test:mutation || echo "Mutation tests failed"

echo "=== Contract Tests ==="
make test:contract || echo "Contract tests failed"

echo "=== API Fuzz Tests ==="
make test:api-fuzz || echo "API fuzz tests failed"

echo "=== Policy Tests ==="
make policy:test || echo "Policy tests failed"

# Generate SBOM
echo "=== SBOM Generation ==="
make sbom || echo "SBOM generation failed"

# Generate traceability matrix
echo "=== Traceability ==="
make verify:trace || echo "Traceability generation failed"

echo "CI checks completed!"