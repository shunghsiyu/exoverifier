#!/bin/bash
set -e

echo "=== Exoverifier Lean 4 Setup Script ==="
echo ""

# Check if we're in the right directory
if [ ! -f "lakefile.lean" ]; then
    echo "Error: Please run this script from the lean/ directory"
    exit 1
fi

echo "Step 1: Installing elan (Lean version manager)..."
if ! command -v elan &> /dev/null; then
    echo "Installing elan..."
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
    source ~/.elan/env
else
    echo "elan already installed"
fi

echo ""
echo "Step 2: Installing Lean 4.25.0..."
elan toolchain install leanprover/lean4:v4.25.0
elan default leanprover/lean4:v4.25.0

echo ""
echo "Step 3: Updating lake and mathlib dependencies..."
lake update

echo ""
echo "Step 4: Building mathlib (this may take a while)..."
lake build Mathlib

echo ""
echo "Step 5: Building Exoverifier..."
lake build

echo ""
echo "=== Setup Complete! ==="
echo ""
echo "You can now:"
echo "  - Build the project: lake build"
echo "  - Clean build: lake clean && lake build"
echo "  - Check a specific file: lean src/Bpf/Basic.lean"
echo ""
echo "Next steps:"
echo "  1. Review LEAN4_MIGRATION.md for implementation priorities"
echo "  2. Start filling in 'sorry' placeholders with real implementations"
echo "  3. Run 'lake build' frequently to catch errors early"
