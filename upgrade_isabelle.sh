#!/usr/bin/env bash
#
# Upgrade to Isabelle 2025 for AFP compatibility
#

set -e

INSTALL_DIR="${HOME}/isabelle"
OLD_VERSION="Isabelle2024"
NEW_VERSION="Isabelle2025"

echo "🚀 Upgrading Isabelle ${OLD_VERSION} -> ${NEW_VERSION}"
echo "This will download ~1GB and ensure AFP compatibility"
echo ""
read -p "Continue? (y/N) " -n 1 -r
echo

if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Aborted"
    exit 0
fi

cd "$INSTALL_DIR"

# Download Isabelle 2025
echo "Downloading Isabelle ${NEW_VERSION}..."
if [[ "$OSTYPE" == "darwin"* ]]; then
    ISABELLE_URL="https://isabelle.in.tum.de/website-${NEW_VERSION}/dist/${NEW_VERSION}_macos.tar.gz"
elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
    ISABELLE_URL="https://isabelle.in.tum.de/website-${NEW_VERSION}/dist/${NEW_VERSION}_linux.tar.gz"
else
    echo "Unsupported OS: $OSTYPE"
    exit 1
fi

curl -L -o "${NEW_VERSION}.tar.gz" "$ISABELLE_URL"

# Extract
echo "Extracting Isabelle..."
tar -xzf "${NEW_VERSION}.tar.gz"
rm "${NEW_VERSION}.tar.gz"

# Update config
cat > "$INSTALL_DIR/isabelle-config.sh" << EOF
# Isabelle Configuration
# Source this file in your ~/.bashrc or ~/.zshrc

export ISABELLE_HOME="$INSTALL_DIR/$NEW_VERSION"
export PATH="\$ISABELLE_HOME/bin:\$PATH"
EOF

echo "✅ Isabelle ${NEW_VERSION} installed!"
echo ""
echo "Source the new config:"
echo "  source ~/isabelle/isabelle-config.sh"
echo ""
echo "Now run ./setup.sh --skip-isabelle to setup AFP"