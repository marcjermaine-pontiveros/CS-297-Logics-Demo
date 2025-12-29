# Isabelle CLI Verification Guide

## Quick CLI Commands

### 1. **Build All Theories**
```bash
source ~/isabelle/isabelle-config.sh
isabelle build -D . QHL_Tests
```

### 2. **Build with Verbose Output**
```bash
isabelle build -v -D . QHL_Tests
```

### 3. **Check Build Status**
```bash
isabelle build -n -D . QHL_Tests
```

### 4. **View Build Logs**
```bash
# See errors only
isabelle build_log -H Error

# See all logs
isabelle build_log -v
```

### 5. **Quick Syntax Check**
```bash
./verify_generated.sh
```

## Alternative: Use Isabelle/jEdit CLI Mode

If you want to avoid the GUI but still get interactive feedback:

```bash
# Console mode (no GUI)
isabelle build -D . QHL_Tests
```

## Build Output Interpretation

- ✅ **"Finished QHL_Tests"** = All theories verified successfully
- ❌ **"FAILED"** = There are errors in the theories
- ⏳ **Long wait time** = Normal on first build (compiling dependencies)

## Note on Individual Theory Verification

Isabelle builds **sessions**, not individual theory files. Your theories are in the `QHL_Tests` session, so you build the whole session at once.

## Fastest Verification Method

The **CLI build is the fastest method** once dependencies are compiled. First build takes 5-15 minutes, subsequent builds are much faster.