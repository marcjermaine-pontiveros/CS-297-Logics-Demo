#!/usr/bin/env bash
#
# Batch processing script for Isabelle theory files
#

set -e

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

# Check if Isabelle is installed
if ! command -v isabelle &> /dev/null; then
    print_error "Isabelle not found in PATH"
    print_info "Please run ./setup.sh to install Isabelle"
    exit 1
fi

# Parse command line arguments
BUILD_DIR="."
SESSIONS=""
VERBOSE=false
CLEAN=false

while [[ $# -gt 0 ]]; do
    case $1 in
        -d|--dir)
            BUILD_DIR="$2"
            shift 2
            ;;
        -s|--session)
            SESSIONS="$SESSIONS $2"
            shift 2
            ;;
        -v|--verbose)
            VERBOSE=true
            shift
            ;;
        -c|--clean)
            CLEAN=true
            shift
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS]"
            echo "Options:"
            echo "  -d, --dir DIR       Build directory (default: current directory)"
            echo "  -s, --session NAME  Specific session to build"
            echo "  -v, --verbose       Verbose output"
            echo "  -c, --clean         Clean build"
            echo "  -h, --help          Show this help message"
            exit 0
            ;;
        *)
            print_error "Unknown option: $1"
            exit 1
            ;;
    esac
done

print_info "Isabelle Batch Build"
print_info "Build directory: $BUILD_DIR"

# Find all .thy files
if [ -z "$SESSIONS" ]; then
    THY_FILES=$(find "$BUILD_DIR" -name "*.thy" -type f)
    if [ -z "$THY_FILES" ]; then
        print_warn "No theory files found in $BUILD_DIR"
        exit 0
    fi

    print_info "Found theory files:"
    echo "$THY_FILES" | while read -r file; do
        echo "  - $file"
    done
else
    print_info "Building sessions: $SESSIONS"
fi

# Clean build if requested
if [ "$CLEAN" = true ]; then
    print_info "Cleaning previous builds..."
    isabelle build -C "$BUILD_DIR" -c || true
fi

# Build options
BUILD_OPTS="-D $BUILD_DIR"
if [ "$VERBOSE" = true ]; then
    BUILD_OPTS="$BUILD_OPTS -v"
fi

print_info "Starting build..."
print_info "Command: isabelle build $BUILD_OPTS"

# Run build
if isabelle build $BUILD_OPTS; then
    print_info "Build completed successfully!"
else
    print_error "Build failed!"
    exit 1
fi

# Display results
print_info "Build results:"
echo ""
echo "Session status:"
isabelle build -D "$BUILD_DIR" -n | while read -r line; do
    echo "  $line"
done