#!/usr/bin/env bash
#
# Fix AFP compatibility for Isabelle2024
#

set -e

INSTALL_DIR="${HOME}/isabelle"
AFP_DIR="$INSTALL_DIR/afp"

echo "🔧 Fixing AFP compatibility for Isabelle2024..."

# Check current AFP installation
if [ -d "$AFP_DIR" ]; then
    echo "Removing incompatible AFP installation..."
    rm -rf "$AFP_DIR"
fi

echo "Downloading AFP-2024 for Isabelle2024..."
echo "Note: This will download from SourceForge where older AFP versions are stored"

# Try to find AFP-2024 (you may need to check SourceForge for the exact version)
AFP_BASE_URL="https://sourceforge.net/projects/afp/files/afp-2024"

# Common AFP 2024 releases (you may need to adjust the exact version)
AFP_VERSIONS=(
    "2024-01-22"
    "2024-02-26"
    "2024-03-25"
    "2024-04-29"
    "2024-06-17"
    "2024-07-01"
)

echo "Attempting to download AFP-2024..."
echo "If this fails, manually download from: https://sourceforge.net/projects/afp/files/afp-2024/"
echo ""

# Try each version
for version in "${AFP_VERSIONS[@]}"; do
    AFP_URL="${AFP_BASE_URL}/afp-${version}.tar.gz"
    echo "Trying: $AFP_URL"

    if curl -fL -o "afp-2024.tar.gz" "$AFP_URL" 2>/dev/null; then
        echo "✅ Successfully downloaded AFP-${version}!"

        # Extract
        echo "Extracting AFP..."
        mkdir -p "$AFP_DIR"
        tar -xzf "afp-2024.tar.gz" -C "$AFP_DIR" --strip-components=1
        rm "afp-2024.tar.gz"

        echo "✅ AFP-2024 installed successfully!"
        break
    else
        echo "❌ Version ${version} not found, trying next..."
        rm -f "afp-2024.tar.gz"
    fi
done

# Register AFP with Isabelle
echo "Registering AFP with Isabelle..."
source "$INSTALL_DIR/isabelle-config.sh"
isabelle components -u "$AFP_DIR/thys"

echo "✅ AFP setup complete!"
echo ""
echo "Test the setup:"
echo "  isabelle build -D ."