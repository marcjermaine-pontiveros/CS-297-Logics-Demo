# Setup Guide - Isabelle + AFP Installation

## Prerequisites

- macOS or Linux
- Python 3.8+
- UV package manager (recommended) or pip

## Step 1: Install Isabelle and AFP

### Automated Installation (Recommended)

```bash
# Run the automated setup script
./bin/setup.sh
```

This will:
- Download Isabelle2025
- Download AFP-2025 (March 17, 2025 release)
- Configure environment variables
- Register AFP with Isabelle

### Manual Installation

If the automated script fails:

```bash
# 1. Download Isabelle2025
cd ~/isabelle
curl -L -o Isabelle2025.tar.gz "https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_darwin.tar.gz"
tar -xzf Isabelle2025.tar.gz

# 2. Download AFP-2025
curl -L -o afp-2025.tar.gz "https://www.isa-afp.org/release/afp-2025-03-17.tar.gz"
mkdir -p afp && tar -xzf afp-2025.tar.gz -C afp --strip-components=1

# 3. Register AFP
export ISABELLE_HOME="$HOME/isabelle/Isabelle2025.app"
isabelle components -u ~/isabelle/afp/thys
```

## Step 2: Install Python Dependencies

```bash
# Using UV (recommended)
uv sync

# Or using pip
pip install -r requirements.txt
```

## Step 3: Verify Installation

```bash
# Check Isabelle version
source ~/isabelle/isabelle-config.sh
isabelle version

# Check AFP registration
isabelle components | grep afp

# Test pipeline
python3 qasm_to_isabelle.py examples/hadamard.qasm
```

## Environment Configuration

Add to your `~/.bashrc` or `~//.zshrc`:

```bash
source ~/isabelle/isabelle-config.sh
```

## Troubleshooting

### "AFP session not found"
- Ensure AFP-2025 is installed (not afp-current)
- Re-register: `isabelle components -u ~/isabelle/afp/thys`

### Build errors
- Check AFP version matches Isabelle version
- Verify Jordan_Normal_Form builds: `isabelle build AFP/Jordan_Normal_Form`

### Python import errors
- Ensure dependencies installed: `uv sync`
- Check Python version: `python3 --version`