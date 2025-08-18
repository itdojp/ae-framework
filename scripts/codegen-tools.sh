#!/bin/bash

# AE-Framework Code Generation Tools
# Helper scripts for deterministic code generation and drift management

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

print_colored() {
    local color=$1
    shift
    echo -e "${color}$@${NC}"
}

print_header() {
    echo ""
    print_colored $BLUE "=========================================="
    print_colored $BLUE "$1"
    print_colored $BLUE "=========================================="
}

# Configuration
AE_IR_FILE=".ae/ae-ir.json"
GENERATED_DIR="generated"
SPEC_DIR="spec"

# Function to check prerequisites
check_prerequisites() {
    print_header "Checking Prerequisites"
    
    # Check if ae-framework is built
    if [ ! -f "dist/cli/index.js" ]; then
        print_colored $YELLOW "⚠️  ae-framework not built. Building..."
        npm run build
        print_colored $GREEN "✅ Build completed"
    else
        print_colored $GREEN "✅ ae-framework is built"
    fi
    
    # Check for AE-IR file
    if [ ! -f "$AE_IR_FILE" ]; then
        print_colored $YELLOW "⚠️  No AE-IR file found. Checking for specs..."
        
        if find "$SPEC_DIR" -name "*.md" -type f 2>/dev/null | grep -q .; then
            SPEC_FILE=$(find "$SPEC_DIR" -name "*.md" -type f | head -1)
            print_colored $BLUE "📝 Compiling spec: $SPEC_FILE"
            npx tsx src/cli/index.ts spec compile -i "$SPEC_FILE" -o "$AE_IR_FILE"
            print_colored $GREEN "✅ AE-IR compiled from $SPEC_FILE"
        else
            print_colored $RED "❌ No specification files found in $SPEC_DIR"
            exit 1
        fi
    else
        print_colored $GREEN "✅ AE-IR file found: $AE_IR_FILE"
    fi
}

# Function to generate all target types
generate_all() {
    print_header "Generating All Target Types"
    
    local targets=("typescript" "react" "api" "database")
    local generated_count=0
    
    for target in "${targets[@]}"; do
        local target_dir="$GENERATED_DIR/$target"
        print_colored $BLUE "🏗️  Generating $target code..."
        
        mkdir -p "$target_dir"
        
        if npx tsx src/cli/index.ts codegen generate \
            -i "$AE_IR_FILE" \
            -o "$target_dir" \
            -t "$target"; then
            print_colored $GREEN "✅ $target generation completed"
            generated_count=$((generated_count + 1))
        else
            print_colored $RED "❌ $target generation failed"
        fi
        echo ""
    done
    
    print_colored $GREEN "🎉 Generated code for $generated_count/${#targets[@]} targets"
}

# Function to check drift across all targets  
check_drift_all() {
    print_header "Checking Drift Across All Targets"
    
    local total_drift="no_drift"
    local checked_targets=0
    
    if [ ! -d "$GENERATED_DIR" ]; then
        print_colored $YELLOW "⚠️  No generated directory found"
        return 0
    fi
    
    for target_dir in "$GENERATED_DIR"/*; do
        if [ -d "$target_dir" ]; then
            local target_name=$(basename "$target_dir")
            print_colored $BLUE "🔍 Checking drift in $target_name..."
            
            # Run drift detection and capture exit code
            local drift_status="no_drift"
            if npx tsx src/cli/index.ts codegen drift \
                -d "$target_dir" \
                -s "$AE_IR_FILE" 2>/dev/null; then
                drift_status="no_drift"
            else
                case $? in
                    1) drift_status="minor_drift" ;;
                    2) drift_status="major_drift" ;;
                    3) drift_status="critical_drift" ;;
                    *) drift_status="unknown" ;;
                esac
            fi
            
            case "$drift_status" in
                "critical_drift")
                    print_colored $RED "🚨 Critical drift in $target_name"
                    total_drift="critical_drift"
                    ;;
                "major_drift")
                    print_colored $RED "🟠 Major drift in $target_name"
                    if [ "$total_drift" != "critical_drift" ]; then
                        total_drift="major_drift"
                    fi
                    ;;
                "minor_drift")
                    print_colored $YELLOW "⚠️  Minor drift in $target_name"
                    if [ "$total_drift" = "no_drift" ]; then
                        total_drift="minor_drift"
                    fi
                    ;;
                "no_drift")
                    print_colored $GREEN "✅ No drift in $target_name"
                    ;;
                *)
                    print_colored $YELLOW "❓ Unknown drift status in $target_name"
                    ;;
            esac
            
            checked_targets=$((checked_targets + 1))
        fi
    done
    
    # Summary
    echo ""
    case "$total_drift" in
        "no_drift")
            print_colored $GREEN "🎉 No drift detected across $checked_targets targets"
            ;;
        "minor_drift")
            print_colored $YELLOW "⚠️  Minor drift detected. Consider regenerating code."
            ;;
        "major_drift")
            print_colored $RED "🟠 Major drift detected. Regeneration recommended."
            ;;
        "critical_drift")
            print_colored $RED "🚨 Critical drift detected. Immediate regeneration required."
            ;;
    esac
    
    return 0
}

# Function to regenerate drifted code
regenerate_drifted() {
    print_header "Regenerating Drifted Code"
    
    local regenerated_count=0
    
    for target_dir in "$GENERATED_DIR"/*; do
        if [ -d "$target_dir" ]; then
            local target_name=$(basename "$target_dir")
            
            # Check if this target has drift
            if ! npx tsx src/cli/index.ts codegen drift \
                -d "$target_dir" \
                -s "$AE_IR_FILE" >/dev/null 2>&1; then
                
                print_colored $BLUE "🔄 Regenerating $target_name due to drift..."
                
                if npx tsx src/cli/index.ts codegen generate \
                    -i "$AE_IR_FILE" \
                    -o "$target_dir" \
                    -t "$target_name"; then
                    print_colored $GREEN "✅ $target_name regenerated successfully"
                    regenerated_count=$((regenerated_count + 1))
                else
                    print_colored $RED "❌ Failed to regenerate $target_name"
                fi
            else
                print_colored $GREEN "⏭️  $target_name is up to date"
            fi
        fi
    done
    
    if [ $regenerated_count -eq 0 ]; then
        print_colored $GREEN "🎉 All code is up to date, no regeneration needed"
    else
        print_colored $GREEN "🎉 Regenerated $regenerated_count targets"
    fi
}

# Function to watch for changes and auto-regenerate
watch_and_regenerate() {
    print_header "Starting Watch Mode"
    
    print_colored $BLUE "👀 Watching for changes in:"
    print_colored $GRAY "   - $AE_IR_FILE"
    print_colored $GRAY "   - $SPEC_DIR/**/*.md"
    print_colored $YELLOW "   Press Ctrl+C to stop"
    
    # Check if chokidar-cli is available
    if ! command -v chokidar &> /dev/null; then
        print_colored $YELLOW "⚠️  chokidar-cli not found, installing..."
        npm install -g chokidar-cli
    fi
    
    chokidar "$AE_IR_FILE" "$SPEC_DIR/**/*.md" -c "bash $0 regenerate-drifted"
}

# Function to validate generated code
validate_generated() {
    print_header "Validating Generated Code"
    
    local validation_errors=0
    
    # Validate TypeScript
    if [ -d "$GENERATED_DIR/typescript" ]; then
        print_colored $BLUE "🔍 Validating TypeScript code..."
        cd "$GENERATED_DIR/typescript"
        
        if ls *.ts 1> /dev/null 2>&1; then
            if npx tsc --noEmit --skipLibCheck *.ts 2>/dev/null; then
                print_colored $GREEN "✅ TypeScript validation passed"
            else
                print_colored $RED "❌ TypeScript validation failed"
                validation_errors=$((validation_errors + 1))
            fi
        else
            print_colored $YELLOW "⚠️  No TypeScript files found"
        fi
        cd - > /dev/null
    fi
    
    # Validate React components
    if [ -d "$GENERATED_DIR/react" ]; then
        print_colored $BLUE "🔍 Validating React components..."
        cd "$GENERATED_DIR/react"
        
        if ls *.tsx 1> /dev/null 2>&1; then
            local react_errors=0
            for file in *.tsx; do
                if [ -f "$file" ]; then
                    if ! npx tsc --noEmit --skipLibCheck --jsx react "$file" 2>/dev/null; then
                        print_colored $RED "❌ $file validation failed"
                        react_errors=$((react_errors + 1))
                    fi
                fi
            done
            
            if [ $react_errors -eq 0 ]; then
                print_colored $GREEN "✅ React components validation passed"
            else
                print_colored $RED "❌ React validation failed ($react_errors errors)"
                validation_errors=$((validation_errors + 1))
            fi
        else
            print_colored $YELLOW "⚠️  No React components found"
        fi
        cd - > /dev/null
    fi
    
    # Summary
    if [ $validation_errors -eq 0 ]; then
        print_colored $GREEN "🎉 All validations passed"
        return 0
    else
        print_colored $RED "❌ Validation failed with $validation_errors errors"
        return 1
    fi
}

# Function to show generation status
show_status() {
    print_header "Code Generation Status"
    
    if [ -f "$AE_IR_FILE" ]; then
        print_colored $GREEN "✅ AE-IR: $AE_IR_FILE"
        # Show spec hash and timestamp
        if command -v jq &> /dev/null; then
            local spec_name=$(jq -r '.metadata.name' "$AE_IR_FILE" 2>/dev/null || echo "Unknown")
            local updated=$(jq -r '.metadata.updated' "$AE_IR_FILE" 2>/dev/null || echo "Unknown")
            print_colored $GRAY "   Name: $spec_name"
            print_colored $GRAY "   Updated: $updated"
        fi
    else
        print_colored $RED "❌ No AE-IR file found"
    fi
    
    echo ""
    print_colored $BLUE "Generated Code:"
    if [ -d "$GENERATED_DIR" ]; then
        for target_dir in "$GENERATED_DIR"/*; do
            if [ -d "$target_dir" ]; then
                local target_name=$(basename "$target_dir")
                local file_count=$(find "$target_dir" -name "*.ts" -o -name "*.tsx" -o -name "*.js" -o -name "*.sql" | wc -l)
                
                # Check if manifest exists
                if [ -f "$target_dir/.codegen-manifest.json" ]; then
                    local generated_at=$(jq -r '.metadata.generatedAt' "$target_dir/.codegen-manifest.json" 2>/dev/null || echo "Unknown")
                    print_colored $GREEN "✅ $target_name: $file_count files (Generated: $generated_at)"
                else
                    print_colored $YELLOW "⚠️  $target_name: $file_count files (No manifest)"
                fi
            fi
        done
    else
        print_colored $YELLOW "⚠️  No generated code found"
    fi
}

# Function to clean generated code
clean_generated() {
    print_header "Cleaning Generated Code"
    
    if [ -d "$GENERATED_DIR" ]; then
        print_colored $YELLOW "🧹 Removing generated code directory..."
        rm -rf "$GENERATED_DIR"
        print_colored $GREEN "✅ Generated code cleaned"
    else
        print_colored $GREEN "✅ No generated code to clean"
    fi
}

# Show help
show_help() {
    echo "AE-Framework Code Generation Tools"
    echo ""
    echo "USAGE:"
    echo "  $0 <command>"
    echo ""
    echo "COMMANDS:"
    echo "  generate-all       Generate code for all targets (typescript, react, api, database)"
    echo "  check-drift        Check for drift across all generated code"
    echo "  regenerate-drifted Regenerate only code that has drifted"
    echo "  watch              Watch for changes and auto-regenerate"
    echo "  validate           Validate generated code"
    echo "  status             Show current generation status"
    echo "  clean              Clean all generated code"
    echo "  help               Show this help message"
    echo ""
    echo "EXAMPLES:"
    echo "  $0 generate-all    # Generate all target types"
    echo "  $0 check-drift     # Check for drift in existing code"
    echo "  $0 watch           # Watch for changes and auto-regenerate"
    echo ""
}

# Main execution
main() {
    case "${1:-help}" in
        "generate-all"|"gen-all"|"generate")
            check_prerequisites
            generate_all
            ;;
        "check-drift"|"drift"|"check")
            check_prerequisites
            check_drift_all
            ;;
        "regenerate-drifted"|"regen"|"regenerate")
            check_prerequisites
            regenerate_drifted
            ;;
        "watch")
            check_prerequisites
            watch_and_regenerate
            ;;
        "validate"|"val")
            validate_generated
            ;;
        "status"|"stat")
            show_status
            ;;
        "clean")
            clean_generated
            ;;
        "help"|"-h"|"--help")
            show_help
            ;;
        *)
            print_colored $RED "Unknown command: $1"
            echo ""
            show_help
            exit 1
            ;;
    esac
}

# Run main function
main "$@"