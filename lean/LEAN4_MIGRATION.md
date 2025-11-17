# Lean 4 Migration Status

This document tracks the migration of Exoverifier from Lean 3 to Lean 4.

## Overview

Exoverifier is a proof-carrying code framework for eBPF programs. The migration to Lean 4 establishes the foundational structure while preserving the architecture and design of the original Lean 3 implementation.

## Migration Strategy

**Iterative Approach**: Migrate layer by layer, from foundational utilities up to high-level verification components. Commit frequently to track progress and enable incremental testing.

**Placeholder Pattern**: For complex implementations, create skeleton files with proper structure and type signatures, marking detailed implementations as `sorry` or placeholders. This allows:
- Early detection of architecture issues
- Incremental refinement
- Clear documentation of what needs implementation

## Completed Migrations

### ✅ Layer 1: Build Configuration
- **Files**: `lean-toolchain`, `lakefile.lean`
- **Status**: Complete
- **Notes**:
  - Lean 4.25.0 specified
  - Mathlib4 dependency configured
  - Lake build system (replaces leanpkg)

### ✅ Layer 2: Misc Utilities (Foundation)
- **Directory**: `Misc/`
- **Files**: 13 files
- **Status**: Core utilities complete, some need detailed implementation
- **Completed**:
  - `Bool.lean`: Boolean utilities and full adder
  - `Eq.lean`: Conditional function extensionality
  - `Option.lean`: Option extensions
  - `List.lean`: List utilities and theorems
  - `Fin.lean`: Fin utilities (some proofs as sorry)
  - `OrderedState.lean`: Ordered state monad
  - `WithBot.lean`, `WithTop.lean`: Bounded types
- **Placeholders** (need implementation):
  - `Vector.lean`: Vector operations (Lean 4 uses different approach)
  - `FinEnum.lean`: Finite enumeration (different in Lean 4)
  - `SemiDecision.lean`: Semi-decision procedures
  - `TestTree.lean`: Testing utilities

### ✅ Layer 3: Bitvectors (Data/Bv)
- **Directory**: `Data/Bv/`
- **Files**: 11 files
- **Status**: Structure complete, implementations need refinement
- **Core**:
  - `Basic.lean`: Core bitvector type `Fin n → Bool`, conversions (toNat, ofNat, toFin)
  - Instances: Bot, Top, Zero, One, Complement, Inf, Sup, Add, Neg, Mul
  - Many proofs marked as `sorry` for iterative completion
- **Operations** (placeholders):
  - `Order.lean`: Comparison operations
  - `Concat.lean`: Concatenation, drop, take
  - `Adc.lean`, `Sbc.lean`: Add/subtract with carry
  - `Mul.lean`, `Div.lean`: Multiplication, division
  - `Int.lean`: Signed operations
  - `Circuit.lean`, `Vector.lean`: Circuit and vector operations
  - `All.lean`: Imports all modules

### ✅ Layer 4: Abstract Domains (Data/Domain)
- **Directory**: `Data/Domain/`
- **Files**: 5 files
- **Status**: Framework complete, domain implementations need work
- **Framework**:
  - `Basic.lean`: Abstract domain framework
    - `HasGamma`: Abstraction function (α → Set β)
    - `AbstrLe`, `AbstrTop`, `AbstrBot`: Lattice structure
    - `AbstrJoin`, `AbstrMeet`: Lattice operations
    - `AbstrUnaryTest`, `AbstrBinaryTest`: Test functions
    - `AbstrUnaryOp`, `AbstrBinaryOp`: Abstract operations
- **Domains** (placeholders):
  - `Tnum.lean`: Tracked number domain (used in Linux BPF verifier)
  - `Trit.lean`: Three-valued logic
  - `WrappedInterval.lean`: Interval domain for modular arithmetic
  - `Bv.lean`: Concrete bitvector domain

### ✅ Layer 5: Data Structures
- **Directories**: `Data/Trie/`, `Data/UnorderedMap/`, `Data/`
- **Files**: 10 files
- **Status**: Placeholders created
- **Components**:
  - **Trie**: Binary trie data structure (3 files)
  - **UnorderedMap**: Generic map interface (3 files)
    - `Basic.lean`: Interface
    - `Trie.lean`: Trie-based implementation
    - `Alist.lean`: Association list implementation
  - **Utilities**: Cache, Counter, Hashable, Option/Order

### ✅ Layer 6: Factory Pattern
- **Directory**: `Factory/`
- **Files**: 1 file
- **Status**: Placeholder
- **Notes**: Abstract factory interface for circuit/formula building

### ✅ Layer 7: SAT Infrastructure
- **Directory**: `Sat/`
- **Files**: 9 files
- **Status**: Structure complete, implementations needed
- **Components**:
  - `Basic.lean`: Core SAT definitions (satisfiability, assignments)
  - `Bool.lean`: Boolean formulas
  - `Cnf.lean`: Conjunctive Normal Form
  - `Dpll.lean`: DPLL SAT solver
  - `Proof.lean`: Proof certificates (DRAT, LRAT)
  - `Factory.lean`: SAT formula factory
  - `Parser.lean`: DIMACS CNF parser
  - `Tactic.lean`: SAT-based tactics (needs Lean 4 metaprogramming rewrite)
  - `Default.lean`: Module aggregator

### ✅ Layer 8: SMT/Bitblasting
- **Directory**: `Smt/Bitblast/`
- **Files**: 21 files
- **Status**: Structure complete, implementations needed
- **Operations**:
  - Core: `Basic.lean`, `Var.lean`, `Const.lean`
  - Arithmetic: `Add`, `Sub`, `Mul`, `Udiv`
  - Logical: `And`, `Or`, `Xor`, `Not`
  - Comparison: `Eq`, `Ult`
  - Control: `Ite`
  - Bit manipulation: `Concat`, `Extract`, `Shl`, `Lshr`, `Redor`
  - `Default.lean`: Imports all
- **Factory**: `Smt/Factory.lean`

### ✅ Layer 9: AIG (And-Inverter Graphs)
- **Directory**: `Aig/`
- **Files**: 7 files
- **Status**: Structure complete, implementations needed
- **Components**:
  - `Basic.lean`: Core AIG data structure
  - `Factory.lean`: AIG construction
  - `ToCnf.lean`: AIG to CNF conversion
  - `Rewrite.lean`: AIG optimization
  - `Aiger.lean`: AIGER format support
  - `Dot.lean`: Graphviz visualization
  - `Default.lean`: Module aggregator

### ✅ Layer 10: BTOR
- **Directory**: `Btor/`
- **Files**: 4 files
- **Status**: Placeholders
- **Components**: Basic, Compile, Factory, Inj

### ✅ Layer 11: Tactics
- **Directory**: `Tactic/`
- **Files**: 2 files
- **Status**: Placeholders (needs complete rewrite for Lean 4)
- **Note**: Lean 4 metaprogramming is fundamentally different from Lean 3

### ✅ Layer 12: BPF Core (★ Main Component)
- **Directory**: `Bpf/`
- **Files**: 12 files across 3 subdirectories
- **Status**: Core structure complete, detailed implementations needed

#### Core BPF (`Bpf/`)
- **`Basic.lean`**: Core BPF definitions
  - Types: `I64`, `I32` (bitvectors)
  - `Oracle`: Nondeterministic execution oracle
  - `Reg`: 12 BPF registers (R0-R9, FP, AX)
  - `InsnClass`: Instruction classes (alu, jmp, ld, ldx, st, stx)
  - `AluOp`: ALU operations (add, sub, mul, div, or_, and_, lsh, rsh, neg, mod, xor, mov, arsh)
  - `JmpOp`: Jump operations (ja, jeq, jgt, jge, jset, jne, jsgt, jsge, call, exit, jlt, jle, jslt, jsle)
  - `Value`: BPF values (scalar, pointer, uninitialized)
- **Other core files** (placeholders):
  - `Spec.lean`: Safety specification
  - `Cfg.lean`: Control flow graph
  - `Decode.lean`: Binary decoder
  - `Decision.lean`: Decision procedures

#### Abstract Interpretation (`Bpf/Absint/`)
- **Purpose**: Abstract interpretation-based verifier (similar to Linux kernel BPF verifier)
- **Files**: 3 files
  - `Basic.lean`: Core absint infrastructure
  - `Value.lean`: Abstract value domain
  - `Regs.lean`: Register state tracking

#### Symbolic Execution (`Bpf/Se/`)
- **Purpose**: Symbolic execution + SAT based verifier (more powerful, handles relational properties)
- **Files**: 4 files
  - `Basic.lean`: Core symbolic execution
  - `SymbolicValue.lean`: Symbolic value representation
  - `Soundness.lean`: Soundness proofs
  - `Default.lean`: Module aggregator

## Migration Statistics

- **Total commits**: 8
- **Files created**: ~170+
- **Layers completed**: 12/12 (structure)
- **Lines of code**: ~2,500+ (skeleton)
- **Original Lean 3 LOC**: ~10,300

## Next Steps

### Phase 1: Core Implementation (Priority)
1. **Bitvector Operations** (`Data/Bv/Basic.lean`)
   - Complete proof for core conversions (toNat, ofNat)
   - Implement arithmetic operations with proofs
   - Add shift and bitwise operations

2. **Abstract Domain Framework** (`Data/Domain/`)
   - Implement Tnum domain (critical for absint verifier)
   - Complete domain operation proofs

3. **BPF Semantics** (`Bpf/Basic.lean`)
   - Complete instruction type definitions
   - Implement execution semantics
   - Define memory model

### Phase 2: Data Structures
4. **Trie Implementation** (`Data/Trie/Basic.lean`)
   - Port the ~2000 line trie implementation
   - This is used extensively for efficient maps

5. **Vector Operations** (`Misc/Vector.lean`)
   - Adapt to Lean 4's Array/Vector approach
   - Many BPF operations depend on this

### Phase 3: Verification Components
6. **SAT Solver** (`Sat/Dpll.lean`)
   - Implement DPLL algorithm
   - Add proof certificate checking

7. **Bit-blasting** (`Smt/Bitblast/`)
   - Implement bit-blasting for each operation
   - Connect to SAT solver

8. **AIG Operations** (`Aig/`)
   - Implement AIG construction and manipulation
   - Add rewriting rules

### Phase 4: Verifiers
9. **Abstract Interpretation Verifier** (`Bpf/Absint/`)
   - Implement abstract domain operations
   - Complete value tracking logic

10. **Symbolic Execution Verifier** (`Bpf/Se/`)
    - Implement symbolic execution engine
    - Complete soundness proofs

### Phase 5: Integration & Testing
11. **Test Migration** (not started)
    - Migrate test files from `lean/test/`
    - Adapt to Lean 4 testing framework

12. **Build Scripts**
    - Update `make_proof.py` for Lean 4
    - Update build dependencies

13. **Documentation**
    - Update README for Lean 4
    - Document API changes

## Known Issues & Differences from Lean 3

### Type System Changes
- **Bool vs bool**: Lean 4 uses `Bool` (capitalized)
- **Nat vs ℕ**: Both work, but `Nat` is canonical
- **Fin changes**: Some operations renamed/restructured

### Syntax Changes
- **Arrows**: `→` remains, but function syntax uses `fun` instead of `λ`
- **Instances**: `instance : Type where` instead of `instance : Type :=`
- **Deriving**: `deriving DecidableEq` instead of `@[derive decidable_eq]`

### Library Changes
- **Mathlib4**: Completely restructured from Mathlib3
  - `data.X` → `Mathlib.Data.X`
  - Many lemma names changed
  - Some tactics replaced

### Metaprogramming
- **Complete rewrite needed**: Lean 4 metaprogramming is fundamentally different
- **Tactics**: All custom tactics need reimplementation
- **Reflection**: `pexpr`, `expr` replaced with new `Expr` system

### Missing Features (Temporary)
- Some proofs use `sorry` - to be filled iteratively
- Metaprogramming components are placeholders
- Some utility functions need adaptation

## Testing

Currently no automated testing due to missing Lean 4 installation in environment.
Once Lean 4 is properly installed:

```bash
cd lean
lake build        # Build the project
lake test         # Run tests (once migrated)
```

## Contributing to Migration

When implementing placeholders:
1. Start with the type signatures and structure
2. Use `sorry` for complex proofs initially
3. Add `-- TODO:` comments for implementation notes
4. Test incrementally with `lake build`
5. Commit frequently with clear messages

## References

- [Lean 4 Documentation](https://lean-lang.org/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean 3 to 4 Conversion Guide](https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki)
- Original Exoverifier: Lean 3.42.1 with Mathlib

## Commit History

1. Initial Lean 4 migration: lakefile, toolchain, Misc utilities
2. Migrate Data/Bv bitvector layer
3. Migrate Data/Domain abstract domain layer
4. Migrate remaining Data layer structures
5. Migrate Factory and Sat infrastructure
6. Migrate Smt and Aig layers
7. Migrate Btor and Tactic layers
8. Migrate Bpf core layer

---

**Migration Progress**: 🟢 Structure Complete | 🟡 Implementations In Progress
