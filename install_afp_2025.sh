#!/usr/bin/env bash
#
# Download AFP-2025 for Isabelle2025 (released March 17, 2025)
#

set -e

INSTALL_DIR="${HOME}/isabelle"
AFP_DIR="$INSTALL_DIR/afp"

echo "🔧 Downloading AFP-2025 for Isabelle2025 (released March 17, 2025)..."

# Remove current incompatible AFP
if [ -d "$AFP_DIR" ]; then
    echo "Removing incompatible AFP installation..."
    rm -rf "$AFP_DIR"
fi

cd "$INSTALL_DIR"

# Download AFP-2025 (released March 17, 2025 for Isabelle2025)
# Using the exact date from the official release
AFP_RELEASE="afp-2025-03-17"
AFP_URL="https://www.isa-afp.org/release/${AFP_RELEASE}.tar.gz"

echo "Downloading: $AFP_URL"

if curl -fL -o "${AFP_RELEASE}.tar.gz" "$AFP_URL"; then
    echo "✅ Successfully downloaded AFP-2025!"

    # Extract
    echo "Extracting AFP..."
    mkdir -p "$AFP_DIR"
    tar -xzf "${AFP_RELEASE}.tar.gz" -C "$AFP_DIR" --strip-components=1
    rm "${AFP_RELEASE}.tar.gz"

    echo "✅ AFP-2025 installed successfully!"
else
    echo "❌ Failed to download AFP-2025"
    echo "Trying alternative download methods..."

    # Try the sourceforge backup
    ALT_URL="https://sourceforge.net/projects/afp/files/afp-2025/${AFP_RELEASE}.tar.gz"
    echo "Trying: $ALT_URL"

    if curl -fL -o "${AFP_RELEASE}.tar.gz" "$ALT_URL"; then
        echo "✅ Downloaded from SourceForge!"

        mkdir -p "$AFP_DIR"
        tar -xzf "${AFP_RELEASE}.tar.gz" -C "$AFP_DIR" --strip-components=1
        rm "${AFP_RELEASE}.tar.gz"

        echo "✅ AFP-2025 installed successfully!"
    else
        echo "❌ All download attempts failed"
        echo "Please manually download AFP-2025 from: https://www.isa-afp.org/download.html"
        exit 1
    fi
fi

# Re-register AFP with Isabelle
echo "Registering AFP with Isabelle..."
source "$INSTALL_DIR/isabelle-config.sh"
isabelle components -x "$AFP_DIR/thys" 2>/dev/null || true
isabelle components -u "$AFP_DIR/thys"

echo "✅ AFP-2025 setup complete!"
echo ""
echo "Test the build:"
echo "  cd ~/Documents/MSCS/Research\ Projects/cs-297-logics"
echo "  isabelle build -D ."