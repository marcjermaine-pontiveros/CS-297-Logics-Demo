#!/usr/bin/env bash
#
# Quick verification script for generated Isabelle theories
# This checks basic syntax without requiring AFP
#

echo "🔍 Checking generated Isabelle theory files..."

for thy_file in *.thy; do
    if [ -f "$thy_file" ]; then
        echo ""
        echo "✅ Checking: $thy_file"

        # Basic syntax checks
        if grep -q "theory " "$thy_file" && \
           grep -q "imports " "$thy_file" && \
           grep -q "begin" "$thy_file" && \
           grep -q "end" "$thy_file"; then
            echo "  ✓ Basic structure OK"
        else
            echo "  ✗ Missing required elements"
        fi

        # Check for circuit definitions
        if grep -q 'definition.*"' "$thy_file"; then
            echo "  ✓ Circuit definition found"
        else
            echo "  ✗ No circuit definition"
        fi

        # Check for lemmas
        lemma_count=$(grep -c "^lemma " "$thy_file")
        echo "  ✓ Found $lemma_count lemma(s)"

        # Show first few lines
        echo "  Preview (first 5 lines):"
        head -5 "$thy_file" | sed 's/^/    /'
    fi
done

echo ""
echo "🎉 Pipeline verification complete!"
echo ""
echo "📝 Note: To actually build and verify proofs in Isabelle/jEdit:"
echo "   1. Ensure AFP version matches your Isabelle version"
echo "   2. Open any .thy file in Isabelle/jEdit"
echo "   3. The theories will load and verify automatically"