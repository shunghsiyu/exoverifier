# Lean 4 Quick Start Guide

This guide helps you get started with the Lean 4 migration of Exoverifier.

## Prerequisites

- Linux, macOS, or Windows with WSL
- curl or wget
- git
- ~10GB disk space (for Lean 4 and mathlib)

## Installation

### Option 1: Automatic Setup (Recommended)

```bash
cd lean/
./setup-lean4.sh
```

This script will:
1. Install elan (Lean version manager)
2. Install Lean 4.25.0
3. Download and build mathlib4
4. Build Exoverifier

### Option 2: Manual Setup

```bash
# Install elan
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# Restart your shell or run:
source ~/.elan/env

# Install Lean 4.25.0
cd lean/
elan toolchain install leanprover/lean4:v4.25.0
elan default leanprover/lean4:v4.25.0

# Update dependencies
lake update

# Build (first time will be slow due to mathlib)
lake build
```

## Verifying Installation

```bash
# Check Lean version
lean --version
# Should output: Lean (version 4.25.0, ...)

# Check lake (build tool)
lake --version

# Try building a simple file
lean src/Misc/Bool.lean
```

## Project Structure

```
lean/
├── lakefile.lean          # Lake build configuration
├── lean-toolchain         # Specifies Lean 4.25.0
├── src/
│   ├── Misc/             # Utilities (Bool, List, Fin, etc.)
│   ├── Data/             # Data structures and bitvectors
│   │   ├── Bv/           # Bitvector operations
│   │   ├── Domain/       # Abstract domains
│   │   ├── Trie/         # Trie data structure
│   │   └── UnorderedMap/ # Hash maps
│   ├── Factory/          # Factory pattern
│   ├── Sat/              # SAT solver infrastructure
│   ├── Smt/              # SMT bit-blasting
│   ├── Aig/              # And-Inverter Graphs
│   ├── Btor/             # BTOR format
│   ├── Tactic/           # Tactic utilities
│   └── Bpf/              # BPF semantics and verifiers
│       ├── Absint/       # Abstract interpretation
│       └── Se/           # Symbolic execution
└── test/                 # Tests (not yet migrated)
```

## Common Commands

```bash
# Build entire project
lake build

# Build specific library
lake build Exoverifier

# Clean build artifacts
lake clean

# Update dependencies
lake update

# Check a specific file
lean src/Bpf/Basic.lean

# Run Lean server (for editor integration)
lean --server
```

## Development Workflow

### 1. Check Current Status

```bash
# See what compiles
lake build 2>&1 | tee build.log

# Count remaining 'sorry' placeholders
grep -r "sorry" src/ | wc -l
```

### 2. Pick a Module to Implement

See `LEAN4_MIGRATION.md` for priorities. Recommended starting points:

- **Easy**: `Misc/Bool.lean` - Boolean utilities (mostly done)
- **Medium**: `Data/Bv/Basic.lean` - Bitvector operations
- **Hard**: `Bpf/Basic.lean` - BPF semantics

### 3. Implement and Test

```bash
# Edit a file
vim src/Data/Bv/Basic.lean

# Check syntax
lean src/Data/Bv/Basic.lean

# Build to check dependencies
lake build

# Commit when working
git add src/Data/Bv/Basic.lean
git commit -m "Implement toNat conversions in Bv/Basic"
```

### 4. Common Patterns

#### Replace `sorry` with implementation:

```lean
-- Before:
theorem toNat_le (v : Fin n → Bool) :
    toNat v ≤ 2^n - 1 := by
  sorry

-- After:
theorem toNat_le (v : Fin n → Bool) :
    toNat v ≤ 2^n - 1 := by
  induction n with
  | zero => simp [toNat]
  | succ n ih =>
    calc toNat v
        = 2 * toNat (Fin.tail v) + cond (v 0) 1 0 := by rw [toNat_succ]
      _ ≤ 2 * (2^n - 1) + 1 := by omega
      _ = 2^n.succ - 1 := by ring
```

## Editor Setup

### VSCode (Recommended)

1. Install [VSCode](https://code.visualstudio.com/)
2. Install extension: "lean4" (by leanprover)
3. Open the `lean/` folder
4. VSCode will detect the lean-toolchain and start the Lean server

### Emacs

```elisp
;; Install lean4-mode
(use-package lean4-mode
  :straight (lean4-mode
             :type git
             :host github
             :repo "leanprover/lean4-mode"))
```

### Vim/Neovim

Install [lean.nvim](https://github.com/Julian/lean.nvim)

## Troubleshooting

### "lake: command not found"

```bash
source ~/.elan/env
# Or restart your shell
```

### "unknown package 'Mathlib'"

```bash
lake update
```

### Build is very slow

First build will be slow (30-60 minutes) as it builds mathlib.
Subsequent builds are incremental and much faster.

### Out of memory during build

```bash
# Limit parallel jobs
lake build -j 2
```

### "unknown identifier" errors

Check imports at top of file:
```lean
import Mathlib.Data.Fin.Basic
import Data.Bv.Basic
```

## Getting Help

- **Lean 4 Documentation**: https://lean-lang.org/lean4/doc/
- **Mathlib4 Docs**: https://leanprover-community.github.io/mathlib4_docs/
- **Lean Zulip Chat**: https://leanprover.zulipchat.com/
- **Migration Guide**: `LEAN4_MIGRATION.md`

## Next Steps

1. Read `LEAN4_MIGRATION.md` for detailed status and priorities
2. Pick a module from Phase 1 (Core Implementation)
3. Start replacing `sorry` with real implementations
4. Run `lake build` frequently
5. Commit often!

Happy proving! 🎉
