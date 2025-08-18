#!/bin/bash

# AE-Framework Specification Validation Script
# Validates all AE-Spec files in the project using the spec-compiler

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
CONFIG_FILE=".ae/spec-validation.config.json"
SPEC_DIR="spec"
RESULTS_DIR="validation-results"

# Function to print colored output
print_colored() {
    local color=$1
    shift
    echo -e "${color}$@${NC}"
}

# Function to print section header
print_header() {
    echo ""
    print_colored $BLUE "=========================================="
    print_colored $BLUE "$1"
    print_colored $BLUE "=========================================="
}

# Function to check prerequisites
check_prerequisites() {
    print_header "Checking Prerequisites"
    
    # Check if spec-compiler is built
    if [ ! -f "packages/spec-compiler/dist/cli.js" ]; then
        print_colored $RED "❌ spec-compiler not found. Building..."
        cd packages/spec-compiler
        npm run build
        cd ../..
        print_colored $GREEN "✅ spec-compiler built successfully"
    else
        print_colored $GREEN "✅ spec-compiler found"
    fi
    
    # Check if config exists
    if [ -f "$CONFIG_FILE" ]; then
        print_colored $GREEN "✅ Validation config found: $CONFIG_FILE"
    else
        print_colored $YELLOW "⚠️  No validation config found, using defaults"
    fi
    
    # Check if spec directory exists
    if [ -d "$SPEC_DIR" ]; then
        SPEC_COUNT=$(find "$SPEC_DIR" -name "*.md" -type f | wc -l)
        print_colored $GREEN "✅ Found $SPEC_COUNT specification files"
    else
        print_colored $RED "❌ No spec directory found at: $SPEC_DIR"
        exit 1
    fi
}

# Function to validate a single spec file
validate_spec() {
    local spec_file=$1
    local base_name=$(basename "$spec_file" .md)
    
    print_colored $BLUE "📋 Validating: $spec_file"
    echo "-------------------------------------------"
    
    # Create results directory if it doesn't exist
    mkdir -p "$RESULTS_DIR"
    
    # Load configuration for quality thresholds
    local max_errors=0
    local max_warnings=10
    
    if [ -f "$CONFIG_FILE" ] && command -v jq &> /dev/null; then
        max_errors=$(jq -r '.quality_gates.max_errors // 0' "$CONFIG_FILE")
        max_warnings=$(jq -r '.quality_gates.max_warnings // 10' "$CONFIG_FILE")
    elif [ -f "$CONFIG_FILE" ] && ! command -v jq &> /dev/null; then
        print_colored $YELLOW "⚠️  'jq' not found. Cannot parse $CONFIG_FILE. Using default validation thresholds."
    fi
    
    # Run validation
    if cd packages/spec-compiler && node dist/cli.js validate -i "../../$spec_file" --max-errors "$max_errors" --max-warnings "$max_warnings"; then
        cd ../..
        print_colored $GREEN "✅ $spec_file passed validation"
        echo "PASSED" > "$RESULTS_DIR/${base_name}.result"
        return 0
    else
        cd ../..
        print_colored $RED "❌ $spec_file failed validation"
        echo "FAILED" > "$RESULTS_DIR/${base_name}.result"
        return 1
    fi
}

# Function to run all validations
run_validations() {
    print_header "Running AE-Spec Validations"
    
    local total_files=0
    local passed_files=0
    local failed_files=0
    local failed_specs=()
    
    # Clean up previous results
    rm -rf "$RESULTS_DIR"
    mkdir -p "$RESULTS_DIR"
    
    # Find all spec files
    while IFS= read -r -d '' spec_file; do
        # Skip files matching exclude patterns if config exists
        local should_skip=false
        if [ -f "$CONFIG_FILE" ] && command -v jq &> /dev/null; then
            while IFS= read -r pattern; do
                if [[ "$spec_file" == $pattern ]]; then
                    should_skip=true
                    break
                fi
            done < <(jq -r '.exclude_patterns[]? // empty' "$CONFIG_FILE")
        fi
        
        if [ "$should_skip" = true ]; then
            print_colored $YELLOW "⏭️  Skipping excluded file: $spec_file"
            continue
        fi
        
        total_files=$((total_files + 1))
        
        if validate_spec "$spec_file"; then
            passed_files=$((passed_files + 1))
        else
            failed_files=$((failed_files + 1))
            failed_specs+=("$spec_file")
        fi
        
        echo ""
    done < <(find "$SPEC_DIR" -name "*.md" -type f -print0)
    
    # Generate summary
    print_header "Validation Summary"
    echo "Total files processed: $total_files"
    print_colored $GREEN "Passed: $passed_files"
    
    if [ $failed_files -gt 0 ]; then
        print_colored $RED "Failed: $failed_files"
        echo ""
        print_colored $RED "Failed specifications:"
        for failed_spec in "${failed_specs[@]}"; do
            print_colored $RED "  - $failed_spec"
        done
        echo ""
        print_colored $YELLOW "💡 Tips for fixing validation issues:"
        print_colored $YELLOW "  - Ensure all entities have at least one required field"
        print_colored $YELLOW "  - Check that invariants reference existing entities"
        print_colored $YELLOW "  - Verify API endpoint format: METHOD /path - Description"
        print_colored $YELLOW "  - Add business rules (invariants) for domain entities"
    else
        print_colored $GREEN "Failed: 0"
    fi
    
    # Save summary
    if [ "$total_files" -eq 0 ]; then
        success_rate=0
    else
        success_rate=$(echo "scale=2; $passed_files * 100 / $total_files" | bc -l 2>/dev/null || echo "0")
    fi
    
    cat > "$RESULTS_DIR/summary.json" << EOF
{
  "timestamp": "$(date -Iseconds)",
  "total_files": $total_files,
  "passed_files": $passed_files,
  "failed_files": $failed_files,
  "success_rate": $success_rate
}
EOF
    
    return $failed_files
}

# Function to show help
show_help() {
    echo "AE-Framework Specification Validation Script"
    echo ""
    echo "USAGE:"
    echo "  $0 [OPTIONS]"
    echo ""
    echo "OPTIONS:"
    echo "  -h, --help     Show this help message"
    echo "  -v, --verbose  Enable verbose output"
    echo "  -q, --quiet    Suppress non-essential output"
    echo "  -f, --file     Validate specific file only"
    echo "  --config       Use specific config file"
    echo "  --no-color     Disable colored output"
    echo ""
    echo "EXAMPLES:"
    echo "  $0                           # Validate all specs"
    echo "  $0 -f spec/my-spec.md      # Validate specific file" 
    echo "  $0 --config custom.json    # Use custom config"
    echo ""
}

# Parse command line arguments
VERBOSE=false
QUIET=false
SPECIFIC_FILE=""
CUSTOM_CONFIG=""

while [[ $# -gt 0 ]]; do
    case $1 in
        -h|--help)
            show_help
            exit 0
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -q|--quiet)
            QUIET=true
            shift
            ;;
        -f|--file)
            SPECIFIC_FILE="$2"
            shift 2
            ;;
        --config)
            CUSTOM_CONFIG="$2"
            CONFIG_FILE="$2"
            shift 2
            ;;
        --no-color)
            # Disable colors
            RED=""
            GREEN=""
            YELLOW=""
            BLUE=""
            NC=""
            shift
            ;;
        *)
            print_colored $RED "Unknown option: $1"
            show_help
            exit 1
            ;;
    esac
done

# Main execution
main() {
    if [ "$QUIET" != true ]; then
        print_header "AE-Framework Specification Validation"
        echo "Config: $CONFIG_FILE"
        echo "Spec Directory: $SPEC_DIR"
    fi
    
    check_prerequisites
    
    if [ -n "$SPECIFIC_FILE" ]; then
        if [ -f "$SPECIFIC_FILE" ]; then
            print_header "Validating Specific File"
            validate_spec "$SPECIFIC_FILE"
            exit $?
        else
            print_colored $RED "❌ File not found: $SPECIFIC_FILE"
            exit 1
        fi
    else
        run_validations
        exit_code=$?
        
        if [ $exit_code -eq 0 ]; then
            print_colored $GREEN "🎉 All specifications passed validation!"
        else
            print_colored $RED "❌ Some specifications failed validation."
            print_colored $YELLOW "Run with individual file validation to see specific issues:"
            print_colored $YELLOW "$0 -f <spec-file.md>"
        fi
        
        exit $exit_code
    fi
}

# Run main function
main "$@"