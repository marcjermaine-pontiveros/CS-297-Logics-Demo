#!/usr/bin/env bash
#
# Installation script for Isabelle and AFP (Archive of Formal Proofs)
# for Quantum Hoare Logic verification
#

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Default installation directory
INSTALL_DIR="${HOME}/isabelle"
ISABELLE_VERSION="Isabelle2024"
AFP_VERSION="current"
SKIP_ISABELLE=false

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -d|--dir)
            INSTALL_DIR="$2"
            shift 2
            ;;
        -v|--version)
            ISABELLE_VERSION="$2"
            shift 2
            ;;
        -s|--skip-isabelle)
            SKIP_ISABELLE=true
            shift
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS]"
            echo "Options:"
            echo "  -d, --dir DIR         Installation directory (default: ~/isabelle)"
            echo "  -v, --version VER     Isabelle version (default: Isabelle2024)"
            echo "  -s, --skip-isabelle   Skip Isabelle download if already installed"
            echo "  -h, --help            Show this help message"
            exit 0
            ;;
        *)
            print_error "Unknown option: $1"
            exit 1
            ;;
    esac
done

print_info "Starting Isabelle and AFP installation..."
print_info "Installation directory: $INSTALL_DIR"
print_info "Isabelle version: $ISABELLE_VERSION"

# Create installation directory
mkdir -p "$INSTALL_DIR"
cd "$INSTALL_DIR"

# Check if Isabelle is already installed
if [ -d "$ISABELLE_VERSION" ]; then
    if [ "$SKIP_ISABELLE" = true ]; then
        print_info "Isabelle already installed, skipping download (--skip-isabelle flag)"
    else
        print_warn "Isabelle already installed in $INSTALL_DIR/$ISABELLE_VERSION"
        read -p "Do you want to re-install? (y/N) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            print_info "Skipping Isabelle installation"
            SKIP_ISABELLE=true
        else
            print_info "Removing existing installation..."
            rm -rf "$ISABELLE_VERSION"
            SKIP_ISABELLE=false  # Need to download since we removed it
        fi
    fi
fi

# Download and install Isabelle
if [ "$SKIP_ISABELLE" = true ]; then
    print_info "Skipping Isabelle download as requested"
elif [ ! -d "$ISABELLE_VERSION" ]; then
    print_info "Downloading Isabelle $ISABELLE_VERSION..."

    # Detect OS
    if [[ "$OSTYPE" == "darwin"* ]]; then
        ISABELLE_URL="https://isabelle.in.tum.de/website-${ISABELLE_VERSION}/dist/${ISABELLE_VERSION}_macos.tar.gz"
    elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
        ISABELLE_URL="https://isabelle.in.tum.de/website-${ISABELLE_VERSION}/dist/${ISABELLE_VERSION}_linux.tar.gz"
    else
        print_error "Unsupported OS: $OSTYPE"
        exit 1
    fi

    print_info "Download URL: $ISABELLE_URL"

    # Download
    if command -v curl &> /dev/null; then
        curl -L -o "${ISABELLE_VERSION}.tar.gz" "$ISABELLE_URL"
    elif command -v wget &> /dev/null; then
        wget -O "${ISABELLE_VERSION}.tar.gz" "$ISABELLE_URL"
    else
        print_error "Neither curl nor wget found. Please install one of them."
        exit 1
    fi

    # Extract
    print_info "Extracting Isabelle..."
    tar -xzf "${ISABELLE_VERSION}.tar.gz"
    rm "${ISABELLE_VERSION}.tar.gz"

    print_info "Isabelle installed successfully!"
else
    print_info "Isabelle already exists, skipping download"
fi

# Set ISABELLE_HOME
export ISABELLE_HOME="$INSTALL_DIR/$ISABELLE_VERSION"
export PATH="$ISABELLE_HOME/bin:$PATH"

print_info "ISABELLE_HOME: $ISABELLE_HOME"

# Download and install AFP
AFP_DIR="$INSTALL_DIR/afp"
if [ -d "$AFP_DIR" ]; then
    print_warn "AFP already installed in $AFP_DIR"
    read -p "Do you want to re-download AFP? (y/N) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        print_info "Removing existing AFP..."
        rm -rf "$AFP_DIR"
    else
        print_info "Using existing AFP installation"
        AFP_EXISTS=true
    fi
fi

if [ ! -d "$AFP_DIR" ]; then
    print_info "Downloading AFP from isa-afp.org (this may take a while)..."
    print_warn "Note: AFP 'current' version is for the latest Isabelle release"
    print_warn "For Isabelle2024, you may need AFP-2024 or an older version"

    # Get the latest AFP release from isa-afp.org
    AFP_URL="https://www.isa-afp.org/release/afp-current.tar.gz"

    # Alternative: Use sourceforge for older versions
    # AFP_URL="https://sourceforge.net/projects/afp/files/afp-2024/afp-2024-xx-xx.tar.gz"

    print_info "Download URL: $AFP_URL"

    # Download AFP
    if command -v curl &> /dev/null; then
        curl -L -o "afp-current.tar.gz" "$AFP_URL"
    elif command -v wget &> /dev/null; then
        wget -O "afp-current.tar.gz" "$AFP_URL"
    else
        print_error "Neither curl nor wget found. Please install one of them."
        exit 1
    fi

    # Extract AFP
    print_info "Extracting AFP..."
    mkdir -p "$AFP_DIR"
    tar -xzf "afp-current.tar.gz" -C "$AFP_DIR" --strip-components=1
    rm "afp-current.tar.gz"

    print_info "AFP downloaded successfully!"
    print_warn "If you experience compatibility issues, download the AFP version matching your Isabelle release"
fi

# Register AFP with Isabelle
print_info "Registering AFP with Isabelle..."
"$ISABELLE_HOME/bin/isabelle" components -u "$AFP_DIR/thys"

# Create configuration file
CONFIG_FILE="$INSTALL_DIR/isabelle-config.sh"
cat > "$CONFIG_FILE" << EOF
# Isabelle Configuration
# Source this file in your ~/.bashrc or ~/.zshrc

export ISABELLE_HOME="$ISABELLE_HOME"
export PATH="\$ISABELLE_HOME/bin:\$PATH"
EOF

print_info "Configuration file created: $CONFIG_FILE"
print_info "Add the following to your ~/.bashrc or ~/.zshrc:"
print_info "  source $CONFIG_FILE"

# Test installation
print_info "Testing Isabelle installation..."
if "$ISABELLE_HOME/bin/isabelle" version &> /dev/null; then
    print_info "Isabelle installation verified!"
    "$ISABELLE_HOME/bin/isabelle" version
else
    print_error "Isabelle installation test failed"
    exit 1
fi

# Test AFP registration
print_info "Testing AFP registration..."
if "$ISABELLE_HOME/bin/isabelle" components | grep -q "afp"; then
    print_info "AFP successfully registered with Isabelle!"
else
    print_warn "AFP registration may have failed. Check manually with: isabelle components"
fi

print_info "Installation complete!"
echo ""
print_info "Next steps:"
echo "  1. Source the configuration: source $CONFIG_FILE"
echo "  2. Open Isabelle/jEdit: isabelle jedit"
echo "  3. Test QHLProver: create a theory file with 'imports \"QHLProver.Quantum_Hoare\"'"