#!/bin/bash
#
# Validate CI/CD Tag Trigger Configuration
# Phase 1.3: Ensures all workflows have proper tag triggers
#

set -euo pipefail

WORKFLOWS_DIR=".github/workflows"
ERRORS=0
WARNINGS=0

echo "🔍 Validating CI/CD Tag Trigger Configuration..."
echo "========================================================"

# Function to check if a workflow has tag triggers
check_workflow_tag_triggers() {
    local workflow_file="$1"
    local workflow_name=$(basename "$workflow_file" .yml)
    
    echo "📋 Checking: $workflow_name"
    
    # Check if workflow has 'on.push.tags' configuration
    local has_tag_trigger=false
    if grep -q "tags:" "$workflow_file" && grep -A5 "tags:" "$workflow_file" | grep -E -q "[\"']?v\*[\"']?"; then
        has_tag_trigger=true
    fi
    
    # Check if workflow has any publish/deploy/release steps
    local has_release_steps=false
    if grep -iq "publish\|deploy\|release" "$workflow_file"; then
        has_release_steps=true
    fi
    
    # Check if workflow has SBOM generation
    local has_sbom=false
    if grep -q "sbom" "$workflow_file"; then
        has_sbom=true
    fi
    
    # Check if workflow has refs/tags references
    local has_refs_tags=false
    if grep -q "refs/tags" "$workflow_file"; then
        has_refs_tags=true
    fi
    
    echo "   Tag triggers: $([ "$has_tag_trigger" = true ] && echo "✅" || echo "❌")"
    echo "   Release steps: $([ "$has_release_steps" = true ] && echo "✅" || echo "❌")"
    echo "   SBOM generation: $([ "$has_sbom" = true ] && echo "✅" || echo "❌")"
    echo "   refs/tags refs: $([ "$has_refs_tags" = true ] && echo "✅" || echo "❌")"
    
    # Validation rules
    if [ "$has_release_steps" = true ] && [ "$has_tag_trigger" = false ]; then
        echo "   ❌ ERROR: Workflow has release steps but no tag triggers!"
        ERRORS=$((ERRORS + 1))
    fi
    
    if [ "$has_refs_tags" = true ] && [ "$has_tag_trigger" = false ]; then
        echo "   ❌ ERROR: Workflow references refs/tags but has no tag triggers!"
        ERRORS=$((ERRORS + 1))
    fi
    
    if [ "$has_sbom" = true ] && [ "$has_tag_trigger" = false ]; then
        echo "   ⚠️  WARNING: Workflow has SBOM generation but no tag triggers"
        WARNINGS=$((WARNINGS + 1))
    fi
    
    # Core CI workflows should have tag triggers for release validation
    if [[ "$workflow_name" == "ci"* ]] || [[ "$workflow_name" == "verify"* ]] || [[ "$workflow_name" == "quality"* ]]; then
        if [ "$has_tag_trigger" = false ]; then
            echo "   ⚠️  WARNING: Core CI workflow should have tag triggers for release validation"
            WARNINGS=$((WARNINGS + 1))
        fi
    fi
    
    echo
}

# Function to validate tag trigger patterns
validate_tag_patterns() {
    echo "🏷️  Validating Tag Trigger Patterns..."
    echo "--------------------------------------"
    
    local valid_patterns=("v*" "'v*'" "\"v*\"" "v[0-9]*" "'v[0-9]*'" "\"v[0-9]*\"")
    local workflows_with_tags=$(find "$WORKFLOWS_DIR" -name "*.yml" -exec grep -l "tags:" {} \;)
    
    for workflow in $workflows_with_tags; do
        local workflow_name=$(basename "$workflow" .yml)
        echo "📋 Checking tag patterns in: $workflow_name"
        
        local tag_lines=$(grep -A3 "tags:" "$workflow" | grep -E "- |tags:")
        echo "   Tag patterns: $tag_lines"
        
        # Check for common mistakes
        if echo "$tag_lines" | grep -Eq "tags:\s*v\*($|\s*)"; then
            echo "   ❌ ERROR: Invalid syntax 'tags: v*' - should be array format!"
            ERRORS=$((ERRORS + 1))
        fi
        
        if echo "$tag_lines" | grep -q "tags: \[.*\]" && ! echo "$tag_lines" | grep -q "'"; then
            echo "   ⚠️  WARNING: Tag pattern without quotes may cause issues"
            WARNINGS=$((WARNINGS + 1))
        fi
        
        echo
    done
}

# Function to check workflow dependencies
check_workflow_dependencies() {
    echo "🔗 Checking Workflow Dependencies..."
    echo "-----------------------------------"
    
    local release_workflow="$WORKFLOWS_DIR/release.yml"
    if [ -f "$release_workflow" ]; then
        echo "📋 Checking release workflow dependencies"
        
        # Check if release workflow depends on CI completion
        if ! grep -q "needs:" "$release_workflow"; then
            echo "   ⚠️  WARNING: Release workflow has no job dependencies"
            WARNINGS=$((WARNINGS + 1))
        fi
        
        # Check if release workflow runs quality gates
        if ! grep -q "quality\|test\|lint" "$release_workflow"; then
            echo "   ⚠️  WARNING: Release workflow doesn't run quality checks"
            WARNINGS=$((WARNINGS + 1))
        fi
    fi
    
    echo
}

# Function to generate recommendations
generate_recommendations() {
    echo "💡 Recommendations for Tag Trigger Configuration:"
    echo "================================================="
    
    echo "1. ✅ Core CI workflows (ci*.yml, verify.yml) should have tag triggers"
    echo "2. ✅ Quality gate workflows should run on tag pushes"
    echo "3. ✅ Use consistent tag pattern: tags: ['v*']"
    echo "4. ✅ Release workflows should depend on CI completion"
    echo "5. ✅ SBOM generation should happen on tagged releases"
    echo
    echo "Example proper configuration:"
    echo "on:"
    echo "  push:"
    echo "    branches: [main, develop]"
    echo "    tags: ['v*'] # Trigger on version tags"
    echo "  pull_request:"
    echo "    branches: [main]"
    echo
}

# Main execution
main() {
    if [ ! -d "$WORKFLOWS_DIR" ]; then
        echo "❌ ERROR: Workflows directory not found: $WORKFLOWS_DIR"
        exit 1
    fi
    
    echo "Found workflows:"
    find "$WORKFLOWS_DIR" -name "*.yml" -not -path "*/node_modules/*" | sort
    echo
    
    # Check each workflow
    while IFS= read -r -d '' workflow; do
        check_workflow_tag_triggers "$workflow"
    done < <(find "$WORKFLOWS_DIR" -name "*.yml" -not -path "*/node_modules/*" -print0)
    
    validate_tag_patterns
    check_workflow_dependencies
    generate_recommendations
    
    # Summary
    echo "📊 Validation Summary:"
    echo "====================="
    echo "Errors: $ERRORS"
    echo "Warnings: $WARNINGS"
    
    if [ $ERRORS -gt 0 ]; then
        echo
        echo "❌ Tag trigger validation failed with $ERRORS errors!"
        exit 1
    elif [ $WARNINGS -gt 0 ]; then
        echo
        echo "⚠️  Tag trigger validation completed with $WARNINGS warnings"
        exit 0
    else
        echo
        echo "✅ All tag triggers configured correctly!"
        exit 0
    fi
}

main "$@"