#!/bin/bash
#
# Docker Image Analysis and Optimization Validator
# Phase 1.4: Analyze Docker image security and performance
#

set -euo pipefail

IMAGE_NAME="ae-framework"
TAG="${1:-latest}"
FULL_IMAGE_NAME="${IMAGE_NAME}:${TAG}"

echo "🐳 Docker Image Analysis for ae-framework"
echo "==========================================="

# Function to check if Docker is available
check_docker() {
    if ! command -v docker >/dev/null 2>&1; then
        echo "❌ Docker is not installed or not in PATH"
        exit 1
    fi
    
    if ! docker info >/dev/null 2>&1; then
        echo "❌ Docker daemon is not running"
        exit 1
    fi
    
    echo "✅ Docker is available"
}

# Function to build the image if it doesn't exist
ensure_image_exists() {
    if ! docker image inspect "$FULL_IMAGE_NAME" >/dev/null 2>&1; then
        echo "🔨 Image $FULL_IMAGE_NAME not found, building..."
        docker build -t "$FULL_IMAGE_NAME" .
    else
        echo "✅ Image $FULL_IMAGE_NAME exists"
    fi
}

# Function to analyze image size
analyze_image_size() {
    echo "📏 Image Size Analysis"
    echo "---------------------"
    
    local image_size=$(docker image inspect "$FULL_IMAGE_NAME" --format='{{.Size}}')
    local size_mb=$((image_size / 1024 / 1024))
    
    echo "Image size: ${size_mb}MB"
    
    if [ $size_mb -lt 200 ]; then
        echo "✅ Image size is excellent (< 200MB)"
    elif [ $size_mb -lt 500 ]; then
        echo "✅ Image size is good (< 500MB)"
    elif [ $size_mb -lt 1000 ]; then
        echo "⚠️  Image size is acceptable (< 1GB)"
    else
        echo "❌ Image size is too large (>= 1GB)"
    fi
    
    echo
    echo "📊 Layer Analysis:"
    docker history "$FULL_IMAGE_NAME" --format "table {{.CreatedBy}}\t{{.Size}}" | head -10
    echo
}

# Function to analyze image layers
analyze_layers() {
    echo "🔍 Layer Analysis"
    echo "-----------------"
    
    local layer_count=$(docker history "$FULL_IMAGE_NAME" --quiet | wc -l)
    echo "Number of layers: $layer_count"
    
    if [ $layer_count -lt 20 ]; then
        echo "✅ Layer count is optimal (< 20 layers)"
    elif [ $layer_count -lt 50 ]; then
        echo "⚠️  Layer count is acceptable (< 50 layers)"
    else
        echo "❌ Too many layers (>= 50 layers)"
    fi
    echo
}

# Function to test security configurations
test_security() {
    echo "🔒 Security Analysis"
    echo "-------------------"
    
    # Test running as non-root user
    local user_check=$(docker run --rm "$FULL_IMAGE_NAME" whoami 2>/dev/null || echo "root")
    
    if [ "$user_check" != "root" ]; then
        echo "✅ Running as non-root user: $user_check"
    else
        echo "❌ Running as root user (security risk)"
    fi
    
    # Check if image has shell access (security consideration)
    local shell_check=$(docker run --rm "$FULL_IMAGE_NAME" which sh 2>/dev/null || echo "not_found")
    
    if [ "$shell_check" = "not_found" ]; then
        echo "✅ No shell access (security hardened)"
    else
        echo "ℹ️  Shell access available at: $shell_check"
    fi
    
    # Test file system permissions
    local fs_check=$(docker run --rm "$FULL_IMAGE_NAME" ls -la /app | head -5)
    echo "File system permissions:"
    echo "$fs_check"
    echo
}

# Function to test application startup
test_application() {
    echo "🚀 Application Testing"
    echo "---------------------"
    
    # Test that the application can start (dry run)
    echo "Testing application startup..."
    
    local container_id=$(docker run -d --rm -p 3001:3000 "$FULL_IMAGE_NAME" 2>/dev/null || echo "failed")
    
    if [ "$container_id" = "failed" ]; then
        echo "❌ Application failed to start"
        return 1
    fi
    
    echo "Container started: $container_id"
    
    # Wait for startup
    sleep 5
    
    # Test health endpoint if available
    if curl -f http://localhost:3001/health >/dev/null 2>&1; then
        echo "✅ Health check passed"
    else
        echo "ℹ️  Health endpoint not available or not responding"
    fi
    
    # Clean up
    docker stop "$container_id" >/dev/null 2>&1 || true
    echo "✅ Application test completed"
    echo
}

# Function to analyze dependencies
analyze_dependencies() {
    echo "📦 Dependency Analysis"
    echo "---------------------"
    
    # Count node_modules in final image
    local node_modules_check=$(docker run --rm "$FULL_IMAGE_NAME" find /app/node_modules -name package.json 2>/dev/null | wc -l || echo "0")
    
    echo "Production dependencies: $node_modules_check packages"
    
    # Check for dev dependencies (should be minimal/none)
    local dev_deps=$(docker run --rm "$FULL_IMAGE_NAME" find /app -name "*.test.*" 2>/dev/null | wc -l || echo "0")
    
    if [ "$dev_deps" -eq 0 ]; then
        echo "✅ No test files found (production optimized)"
    else
        echo "⚠️  Found $dev_deps test files (consider excluding from production image)"
    fi
    
    # Check for source files (should be minimal/none in production)
    local src_files=$(docker run --rm "$FULL_IMAGE_NAME" find /app -name "*.ts" 2>/dev/null | wc -l || echo "0")
    
    if [ "$src_files" -eq 0 ]; then
        echo "✅ No TypeScript source files (production optimized)"
    else
        echo "⚠️  Found $src_files TypeScript files (consider excluding from production image)"
    fi
    echo
}

# Function to generate optimization recommendations
generate_recommendations() {
    echo "💡 Optimization Recommendations"
    echo "==============================="
    
    local image_size=$(docker image inspect "$FULL_IMAGE_NAME" --format='{{.Size}}')
    local size_mb=$((image_size / 1024 / 1024))
    
    if [ $size_mb -gt 500 ]; then
        echo "📉 Size Optimization:"
        echo "  - Consider using distroless base image"
        echo "  - Review and minimize dependencies"
        echo "  - Use .dockerignore to exclude unnecessary files"
        echo
    fi
    
    local layer_count=$(docker history "$FULL_IMAGE_NAME" --quiet | wc -l)
    if [ $layer_count -gt 30 ]; then
        echo "🏗️  Layer Optimization:"
        echo "  - Combine RUN commands to reduce layers"
        echo "  - Use multi-stage builds effectively"
        echo "  - Consider image squashing"
        echo
    fi
    
    echo "🔧 General Recommendations:"
    echo "  - Regularly update base image for security patches"
    echo "  - Use specific version tags instead of 'latest'"
    echo "  - Implement proper health checks"
    echo "  - Set resource limits in production"
    echo "  - Use Docker secrets for sensitive data"
    echo
    
    echo "✅ Phase 1.4 Docker Optimization Complete!"
}

# Main execution
main() {
    check_docker
    ensure_image_exists
    analyze_image_size
    analyze_layers
    test_security
    test_application
    analyze_dependencies
    generate_recommendations
}

# Handle script errors
trap 'echo "❌ Script failed at line $LINENO"' ERR

main "$@"